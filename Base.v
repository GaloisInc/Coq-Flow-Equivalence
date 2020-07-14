Require Import Coq.Arith.PeanoNat.
Open Scope nat_scope.

Require Import Monad.
Import Notations.
Open Scope monad_scope.


Require Import List.
Import ListNotations.
Open Scope list_scope.

Require Export Coq.Sets.Ensembles.
Require Import Setoid.


(** * Decidable equality

Equality is decidable for a type [A] if there is a procedure such that, for any
two elements [a b : A], produces either (1) a proof that [a] equals [b], or (2)
a proof that [a] does not equal [b].

Equality is not decidable for every type [A]; for example, the type of real
numbers is not decidable, but all finite types and most simple inductive types
are decidable.

Types that are decidable can be given instances of the class [eq_dec A]. When
such a type is decidable, the expression [a =? b] is a boolean that can be used
e.g. in an [if] statement: [if a =? b then X else Y]. *)
Class eq_dec A := { Dec : forall (a b : A), {a = b} + {a <> b} }.
Definition eqb {A} `{eq_dec A} (a b : A) : bool :=
  if Dec a b then true else false.
Infix "=?" := eqb.

(** ** Some lemmas about decidable equality *)
Lemma eqb_eq : forall A `{eq_dec A} (a : A), a =? a = true.
Proof. intros. unfold eqb. destruct (Dec a a); auto. Qed.
Lemma eqb_neq : forall A `{eq_dec A} (a b : A), a <> b -> a =? b = false.
Proof. intros. unfold eqb. destruct (Dec a b); auto. contradiction. Qed.

(** ** Instances of decidable equality *)
Instance eq_dec_bool : eq_dec bool.
Proof.
  split. intros [ | ] [ | ]; try (right; inversion 1; fail); try (left; auto; fail).
Defined.

Instance nat_eq_dec : eq_dec nat.
Proof.
  constructor.
  intros x;
  induction x as [ | x]; intros [ | y]; auto.
  destruct (IHx y) as [IHxy | IHxy]; subst; auto.
Defined.

Instance prod_eq_dec {A B} `{eq_dec A} `{eq_dec B} : eq_dec (A*B).
Proof.
  split. intros [a b] [a' b'].
  destruct (Dec a a'); destruct (Dec b b');
    subst; auto;
    right; inversion 1; contradiction.
Defined.

Instance option_eq_dec {A} `{eq_dec A} : eq_dec (option A).
Proof.
  constructor.
  intros [a | ] [b | ];
    try (left; reflexivity);
    try (right; discriminate).
  destruct (Dec a b); subst;
    try (left; reflexivity);
    try (right; inversion 1; contradiction).
Defined.

(** ** Decidable list inclusion

If a type [A] is decidable, then we can also decide whether an element [a] is an
element of a list [ls] of [A]s. This is written [a ∈? ls]. *)

Fixpoint in_list_dec {A} `{eq_dec A} (a : A) (ls : list A) : bool :=
  match ls with
  | [] => false
  | b :: ls' => if a =? b then true else in_list_dec a ls'
  end.
Notation "a ∈ ls" := (in_list_dec a ls = true) (no associativity, at level 90).
Notation "a ∈? ls" := (in_list_dec a ls) (no associativity, at level 90).


(** * Snoc/tail lists

A tail_list is just an ordinary list that is interpreted "backward". In this
development we use it for traces where a trace [t ▶ e] consists of the trace [t]
followed by the event [e].

*)

Inductive tail_list (A : Type) :=
| t_empty : tail_list A
| t_next : tail_list A -> A -> tail_list A.
Arguments t_empty {A}.
Arguments t_next {A}.
Infix "▶" := t_next (left associativity, at level 73).



(** * Ensemble notation

An [Ensemble A] in Coq represents a mathematical set with elements of the type
[A]. [Ensemble]s are defined in the Coq standard library but are not computable,
so we introduce the standard unicode notations below, including [X == Y] to mean
that the sets [X] and [Y] have the same elements.


 *)
Module EnsembleNotation.
  Notation "x ∈ X" := (In _ X x) : ensemble_scope.
  Notation "X ∪ Y" := (Union _ X Y) (at level 50) : ensemble_scope.
  Notation "X ∩ Y" := (Intersection _ X Y) (at level 50) : ensemble_scope.
  Notation "X ⊥ Y" := (Disjoint _ X Y) (at level 90) : ensemble_scope.
  Notation "X ∖ Y" := (Setminus _ X Y) (at level 40) : ensemble_scope.
  Notation "X ⊆ Y" := (Included _ X Y) (at level 80) : ensemble_scope.
  Notation "X == Y" := (Same_set _ X Y) (at level 90) : ensemble_scope.
  Notation "∅" := (Empty_set _) : ensemble_scope.
  Definition singleton {X} (x : X) : Ensemble X := Singleton X x.
  Notation "x ∉ X" := (~(In _ X x)) (at level 70) : ensemble_scope.

  (** ** Decidable set inclusion *)
  Open Scope ensemble_scope.
  Class in_dec {Z} (X : Ensemble Z) := {In_Dec : forall (x:Z), {x ∈ X} + {~(x ∈ X)}}.
  Notation "x ∈? X" := (@In_Dec _ X _ x) : ensemble_scope.
  Arguments In_Dec {Z} X {in_dec}.

  Instance in_dec_singleton {X} `{eq_dec X} {x : X} : in_dec (Singleton _ x).
  Proof.
    constructor.
    intros y.
    destruct (Dec x y).
    - left. subst. constructor.
    - right. inversion 1; contradiction.
  Defined.
  Hint Resolve in_dec_singleton : sets. 


  (** ** Ensembles as a setoid *)

  Lemma Included_refl : forall A (X : Ensemble A), X ⊆ X.
  Proof.
    intros A X. intros x Hx; auto.
  Qed.
  Lemma Included_trans : forall A (X Y Z : Ensemble A), X ⊆ Y -> Y ⊆ Z -> X ⊆ Z.
  Proof.
    intros A X Y Z HXY HYZ x HX.
    apply HYZ. apply HXY. auto.
  Qed.

  Add Parametric Relation A : (Ensemble A) (Included A)
    reflexivity proved by (Included_refl A)
    transitivity proved by (Included_trans A)
    as subset_ensemble_rel.


  Lemma Same_set_refl : forall A (X : Ensemble A), X == X.
  Proof.
    intros A X. split; reflexivity.
  Qed.
  Lemma Same_set_symm : forall A (X Y : Ensemble A), X == Y -> Y == X.
  Proof.
    intros A X Y [HXY HYX]. split.
    * intros y Hy. apply HYX. auto.
    * intros x Hx. apply HXY. auto.
  Qed.
  Lemma Same_set_trans : forall A (X Y Z : Ensemble A), X == Y -> Y == Z -> X == Z.
  Proof.
    intros A X Y Z [HXY HYX] [HYZ HZY].
    split; transitivity Y; auto.
  Qed.


  Add Parametric Relation A : (Ensemble A) (Same_set A)
    reflexivity proved by (Same_set_refl A)
    symmetry proved by (Same_set_symm A)
    transitivity proved by (Same_set_trans A)
    as eq_ensemble_rel.

  Add Parametric Morphism A : (Included A)
    with signature (Same_set A) ==> (Same_set A) ==> iff as subset_mor.
  Proof.
    intros X Y [HXY HYX] X' Y' [HXY' HYX'].
    split; intros H.
    * intros y Hy. apply HXY'. apply H. apply HYX. assumption.
    * intros x HX. apply HYX'. apply H. apply HXY. assumption.
  Qed.

  Add Parametric Morphism A : (In A)
    with signature (Same_set A) ==> (@eq A) ==> iff as in_mor.
  Proof.
    intros X Y [HXY HYX] a.
    split; intros Ha.
    * apply HXY; auto.
    * apply HYX; auto.
  Qed.

  Add Parametric Morphism A : (Union A)
    with signature (Same_set A) ==> (Same_set A) ==> (Same_set A) as union_mor.
  Proof.
    intros X Y HXY X' Y' HXY'.
    split.
    * intros x Hx. inversion Hx; subst; clear Hx.
      + left. rewrite <- HXY. auto.
      + right. rewrite <- HXY'. auto.
    * intros x Hx. inversion Hx; subst; clear Hx.
      + left. rewrite HXY. auto.
      + right. rewrite HXY'. auto.
  Qed.

  Add Parametric Morphism A : (Intersection A)
    with signature (Same_set A) ==> (Same_set A) ==> (Same_set A) as intersection_mor.
  Proof.
    intros X Y HXY X' Y' HXY'.
    split.
    * intros x Hx. inversion Hx; subst; clear Hx.
      split. 
      + rewrite <- HXY. auto.
      + rewrite <- HXY'. auto.
    * intros x Hx. inversion Hx; subst; clear Hx.
      split.
      + rewrite HXY. auto.
      + rewrite HXY'. auto.
  Qed.

  Add Parametric Morphism A : (Disjoint A)
    with signature (Same_set A) ==> (Same_set A) ==> iff as disjoint_mor.
  Proof.
    intros X Y HXY X' Y' HXY'.
    split; intros [Hdisjoint]; constructor; intros x.
    * rewrite <- HXY, <- HXY'. auto.
    * rewrite HXY, HXY'. auto.
  Qed.

  Add Parametric Morphism A : (Setminus A)
    with signature (Same_set A) ==> (Same_set A) ==> (Same_set A) as setminus_mor.
  Proof.
    intros X Y HXY X' Y' HXY'.
    split; intros x [Hx Hx'].
    * split; [rewrite <- HXY; auto | rewrite <- HXY'; auto].
    * split; [rewrite HXY; auto | rewrite HXY'; auto].
  Qed.



  (** ** Helper lemmas *)
  Lemma Setminus_in : forall {A} x (X Y : Ensemble A),
      x ∈ X ∖ Y ->
      x ∈ X.
  Proof.
    intros A x X Y H.
    inversion H; auto.
  Qed.
  Lemma Setminus_not_in : forall {A} x (X Y : Ensemble A),
      x ∈ X ∖ Y ->
      ~(x ∈ Y).
  Proof.
    intros A x X Y H.
    inversion H; auto.
  Qed.
  Hint Resolve Setminus_in Setminus_not_in : sets.

  Lemma not_union_1 : forall {A} (x : A) X Y,
      ~(x ∈ X ∪ Y) ->
      ~(x ∈ X).
  Proof.
    intros A x X Y Hunion HX.
    apply Hunion.
    left.
    assumption.
  Qed.
  Lemma not_union_2 : forall {A} (x : A) X Y,
      ~(x ∈ X ∪ Y) ->
      ~(x ∈ Y).
  Proof.
    intros A x X Y Hunion HX.
    apply Hunion.
    right.
    assumption.
  Qed.
  Hint Resolve not_union_1 not_union_2 : sets.

  Lemma not_in_singleton_neq : forall {A} (x y : A),
      ~(x ∈ singleton y) <->
      x <> y.
  Proof.
    intros x y. split. 
    * intros H_x_y x_y.
      apply H_x_y.
      subst.
      auto with sets.
    * intros x_neq_y.
      inversion 1.
      subst.
      contradiction.
  Qed.
  Hint Resolve not_in_singleton_neq : sets.

  Lemma not_in_setminus : forall {A} (x : A) (X Y : Ensemble A) `{in_dec _ Y},
      x ∉ (X ∖ Y) ->
      (x ∈ Y) \/ x ∉ X.
  Proof.
    intros A x X Y decY Hin.
    destruct (x ∈? Y).
    - left. assumption.
    - right. intro x_in_X.
      apply Hin.
      constructor; auto.
  Qed.

  Lemma in_Y_not_in_setminus_X_Y : forall {A} (x : A) (X Y : Ensemble A),
      (x ∈ Y) ->
      x ∉ (X ∖ Y).
  Proof.
    intros A x X Y HY Hsetminus.
    inversion Hsetminus; contradiction.
  Qed.

  Lemma not_in_X_not_in_setminus_X_Y : forall {A} (x : A) (X Y : Ensemble A),
      x ∉ X ->
      x ∉ (X ∖ Y).
  Proof.
    intros A x X Y HX Hsetminus.
    inversion Hsetminus; contradiction.
  Qed.

  Lemma not_in_union : forall {A} (x : A) X Y,
      x ∉ X ∪ Y <->
      x ∉ X /\ x ∉ Y.
  Proof.
    intros A x X Y.
    split.
    - intros Hunion. split.
      * intros HX. apply Hunion. left. assumption.
      * intros HY. apply Hunion. right. assumption.
    - intros [HX HY] Hunion.
      inversion Hunion; subst; contradiction.
  Qed.


  (** ** Convert from lists to ensembles *)
  Fixpoint from_list {A} (l : list A) : Ensemble A :=
    match l with
    | nil => ∅
    | x :: l' => singleton x ∪ from_list l'
    end.
  Instance from_list_in_dec {A} `{eq_dec A} (l : list A) : in_dec (from_list l).
  Proof.
    constructor. intros a.
    induction l.
    * right. inversion 1.
    * destruct (Dec a a0) as [Heq | Hneq].
      + subst. left. constructor. constructor.
      + destruct IHl as [IHl | IHl].
        ++ left. right. auto.
        ++ right. simpl.
           apply not_in_union.
           split; auto.
           inversion 1; subst; contradiction.
  Defined.

  (** The [all_disjoint ls] predicate asserts that every element of the list
  [ls] is disjoint from every other elemenet of the list [ls]. *)
  Inductive all_disjoint {A} : list A -> Prop :=
  | nil_disjoint : all_disjoint []
  | cons_disjoint x ls : 
      x ∉ from_list ls ->
      all_disjoint ls ->
      all_disjoint (x::ls).


End EnsembleNotation.


(** * Tactics *)

(** ** Inversion *)
Ltac inversion_In :=
  repeat match goal with
  | [ H : In _ [ _ ] |- _ ] => inversion H; subst; clear H
  | [ H : In _ [] |- _ ] => inversion H
  | [ H : In _ (flat_map _ _) |- _ ] => apply in_flat_map in H; destruct H as [? ?]
  | [ H : _ * _ |- _ ] => destruct H as [? ?]
  | [ H : _ /\ _ |- _ ] => destruct H as [? ?]
  | [ H : (_ , _) = (_, _) |- _] => inversion H; subst; clear H
  end.

Ltac case_In :=
  match goal with
  | [ H : In _ [ _ ] |- _ ] => inversion H as [ | H0]
  | [ H : In _ [] |- _ ] => inversion H
  | [ H : In _ (_ :: _) |- _ ] => destruct H as [? | ?]

  | [ H : In _ (_ ++ _) |- _ ] => apply in_app_or in H; destruct H as [H | H]
  end; inversion_In.


Import EnsembleNotation.


(** ** Contradictions *)

(* First, we find contradictions of the form [all_disjoint ls] where [ls] has
more than one occurrence of the same variable. *)

Fixpoint count {A} `{eq_dec A} (a : A) (ls : list A) : nat :=
  match ls with
  | nil => 0
  | cons b ls' => if a =? b then 1+count a ls'
                       else count a ls'
  end.

Lemma count_1_disjoint_contradiction : forall {A} `{eq_dec A} (a:A) ls,
    count a ls > 0 ->
    ~ all_disjoint (a::ls).
Proof.
  induction ls as [ | b ls']; intros Hcount Hdisjoint; simpl in *.
  * inversion Hcount.
  * destruct (Dec a b); subst.
    + inversion Hdisjoint as [ | ? ? Hcontra ]; subst.
      apply Hcontra. left. auto with sets.
    + inversion Hdisjoint as [ | ? ? Ha Hdisjoint']; subst.
      inversion Hdisjoint'; subst.
      apply IHls'; [rewrite eqb_neq in Hcount; auto | ].
      constructor; auto.
      intros Ha_ls'.
      apply Ha.
      right; auto.
Qed.

Lemma count_disjoint_contradiction : forall {A} `{eq_dec A} (a : A) ls,
    count a ls > 1 ->
    ~ all_disjoint ls.
Proof.
  induction ls as [ | b ls']; intros Hcount.
  * inversion Hcount.
  * simpl in Hcount.
    destruct (Dec a b); [subst; rewrite eqb_eq in Hcount | rewrite eqb_neq in Hcount]; auto.
    + apply count_1_disjoint_contradiction.
      apply Gt.gt_S_n; auto.
    + inversion 1; subst.
      apply IHls'; auto.
Qed.


Ltac find_occurrence x ls :=
  match ls with
  | x :: _ => idtac
  | _ :: ?ls' => find_occurrence x ls'
  end.

Ltac find_repetition ls :=
  match ls with
  | context[ ?x :: ?x :: _ ] => constr:(x)
  | context[ ?x :: _  :: ?x :: _ ] => constr:(x)
  | context[ ?x :: _  :: _  :: ?x :: _ ] => constr:(x)
  | context[ ?x :: _  :: _  :: _  :: ?x :: _ ] => constr:(x)
  | context[ ?x :: _  :: _  :: _  :: _  :: ?x :: _ ] => constr:(x)
  | context[ ?x :: _  :: _  :: _  :: _  :: _  :: ?x :: _ ] => constr:(x)
  | context[ ?x :: _  :: _  :: _  :: _  :: _  :: _  :: ?x :: _ ] => constr:(x)
  | context[ ?x :: _  :: _  :: _  :: _  :: _  :: _  :: _  :: ?x :: _ ] => constr:(x)
  | context[ ?x :: _  :: _  :: _  :: _  :: _  :: _  :: _  :: _  :: ?x :: _ ] => constr:(x)
  | context[ ?x :: _  :: _  :: _  :: _  :: _  :: _  :: _  :: _  :: _  :: ?x :: _ ] => constr:(x)
  | context[ ?x :: _  :: _  :: _  :: _  :: _  :: _  :: _  :: _  :: _  :: _  :: ?x :: _ ] => constr:(x)
  | context[ ?x :: _  :: _  :: _  :: _  :: _  :: _  :: _  :: _  :: _  :: _  :: _  :: ?x :: _ ] => constr:(x)
  | context[ ?x :: _  :: _  :: _  :: _  :: _  :: _  :: _  :: _  :: _  :: _  :: _  :: _  :: ?x :: _ ] => constr:(x)
  | context[ ?x :: _  :: _  :: _  :: _  :: _  :: _  :: _  :: _  :: _  :: _  :: _  :: _  :: _  :: ?x :: _ ] => constr:(x)
  | context[ ?x :: _  :: _  :: _  :: _  :: _  :: _  :: _  :: _  :: _  :: _  :: _  :: _  :: _  :: _  :: ?x :: _ ] => constr:(x)
  | context[ ?x :: _  :: _  :: _  :: _  :: _  :: _  :: _  :: _  :: _  :: _  :: _  :: _  :: _  :: _  :: _  :: ?x :: _ ] => constr:(x)
  | context[ ?x :: _  :: _  :: _  :: _  :: _  :: _  :: _  :: _  :: _  :: _  :: _  :: _  :: _  :: _  :: _  :: _  :: ?x :: _ ] => constr:(x)
  | context[ ?x :: _  :: _  :: _  :: _  :: _  :: _  :: _  :: _  :: _  :: _  :: _  :: _  :: _  :: _  :: _  :: _  :: _  :: ?x :: _ ] => constr:(x)
  | context[ ?x :: _  :: _  :: _  :: _  :: _  :: _  :: _  :: _  :: _  :: _  :: _  :: _  :: _  :: _  :: _  :: _  :: _  :: _  :: ?x :: _ ] => constr:(x)

  end.
Lemma reduce_count_cons_eq : forall {A} `{eq_dec A} (x:A) ls n,
    count x ls > n ->
    count x (x :: ls) > S n.
Admitted.
Lemma reduce_count_cons_0 : forall  {A} `{eq_dec A} (x:A) ls,
    count x (x :: ls) > 0.
Admitted.
Lemma reduce_count_cons_neq : forall  {A} `{eq_dec A} (x y : A) ls n,
    count x ls > n ->
    count x (y :: ls) > n.
Admitted.
Ltac reduce_count :=
  repeat match goal with
  | [ |- count ?x (?x :: _) > S ?n ] => apply reduce_count_cons_eq
  | [ |- count ?x (?x :: _) > 0    ] => apply reduce_count_cons_0
  | [ |- count ?x (?y :: _) > ?n   ] => apply reduce_count_cons_neq
  end.
Ltac all_disjoint_contradiction :=
  match goal with
  (* contradiction *)
  | [ H : all_disjoint ?ls |- _ ] => let x := find_repetition ls in
                                     contradict H;
                                     apply (count_disjoint_contradiction x);
                                     reduce_count
  end.

(** ** [find_contradiction]

Use when a hypothesis or collection of hypotheses leads to a simple
contradiction about equality, numbers, or set inclusion that can't be solved by
[contradiction].

*)
Ltac find_contradiction :=
  try contradiction;
  try discriminate;
  try match goal with
  | [ H : ?a = _, H' : ?a = _ |- _ ] => rewrite H in H'; discriminate
  | [ H : ?a = _, H' : _ = ?a |- _ ] => rewrite H in H'; discriminate
  | [ H : _ = ?a, H' : ?a = _ |- _ ] => rewrite <- H in H'; discriminate
  | [ H : _ = ?a, H' : _ = ?a |- _ ] => rewrite H in H'; discriminate
  | [ H : ?a = ?b, H' : ?a <> ?b |- _] => rewrite H in H'; contradiction
  | [ H : ?a = ?b, H' : ?b <> ?a |- _] => rewrite H in H'; contradiction
  | [ H : ?x < ?x |- _ ] => apply Nat.lt_irrefl in H; contradiction
  | [ H : ?x > ?x |- _ ] => apply Nat.lt_irrefl in H; contradiction
  | [ H : ~( ?x ∈ singleton ?x ) |- _ ] => contradict H; auto with sets
  | [ H1 : ?x ∈ ?X1, H2 : ?x ∈ ?X2, H : ?X1 ⊥ ?X2 |- _] =>
      absurd (x ∈ X1 ∩ X2); inversion H; auto with sets; fail
  | [ H : all_disjoint ?ls |- _ ] => all_disjoint_contradiction
  end.




(** ** [decompose_set_structure] and [solve_set]

Use [decompose_set_structure] to deconstruct hypotheses about set inclusion into
simpler hypotheses that can be used to automatically solve a goal.

Use [solve_set] to solve goals of the form [?x ∈ ?X]. May need to combine these;
[decompose_set_structure; solve_set].

*)

Ltac my_subst :=
  match goal with
  | [ H : ?x = ?y |- _ ] => replace y with x in * by auto; clear H
  end.

Ltac decompose_set_structure_1 :=
  match goal with
  | [ H : ?x ∉ ∅ |- _ ] => clear H
  | [ H : ?x ∈ ∅ |- _ ] => inversion H
  | [ H : ?x ∈ ?X ∖ ?Y |- _ ] => destruct H 
  | [ H : ?x ∈ ?X ∪ ?Y |- _ ] => inversion H; subst; clear H
  | [ H : ?x ∈ ?X ∩ ?Y |- _ ] => inversion H; subst; clear H
  | [ H : ~(?x ∈ ?X ∪ ?Y) |- _] => assert (~(x ∈ X)) by auto with sets;
                                   assert (~(x ∈ Y)) by auto with sets;
                                   clear H
  | [ H : ?x ∉ ?X ∖ ?Y |- _ ] => apply not_in_setminus in H; [destruct H | auto with sets]
  | [ H : ?x ∉ ?X ∪ ?Y |- _ ] => apply not_in_union in H; destruct H
  | [ H : ?x ∉ singleton ?y |- _ ] => apply not_in_singleton_neq in H
  | [ H : ?x ∈ Couple _ ?y ?z |- _] => inversion H; try subst; clear H
  | [ H : ?x ∈ singleton ?y |- _ ] => inversion H; my_subst; clear H

(*
  | [ H : all_disjoint [] |- _ ] => clear H
  | [ H : all_disjoint (_ :: _) |- _] => let H' := fresh "H" in
                                         inversion H as [ | ? ? H']; subst; 
                                         simpl in H'; clear H
*)
  | [ H : ?x ∈ from_list _ |- _ ] => simpl in H
  end.
Ltac decompose_set_structure :=
  repeat (decompose_set_structure_1; try find_contradiction; auto with sets).

Ltac try_solve_set :=
  repeat (auto with sets;
  match goal with
  | [ |- ?x <> ?y ] => auto; fail
  | [ |- ?x <> ?y ] => intro; my_subst; all_disjoint_contradiction
  | [ |- ?x ∉ singleton ?y ] => apply not_in_singleton_neq
  | [ |- ?x ∈ ?X ∖ ?Y ] => constructor
  | [ |- ?x ∈ ?X ∪ ?Y ] => left; try_solve_set; fail
  | [ |- ?x ∈ ?X ∪ ?Y ] => right; try_solve_set; fail
  | [ |- ?x ∈ ?X ∩ ?Y ] => constructor
  | [ |- ?x ∉ ?X ∖ ?Y ] => apply in_Y_not_in_setminus_X_Y; try_solve_set; fail
  | [ |- ?x ∉ ?X ∖ ?Y ] => apply not_in_X_not_in_setminus_X_Y; try_solve_set; fail
  | [ |- ?x ∉ ?X ∪ ?Y ] => apply not_in_union; constructor
  | [ |- ?x ∉ ?X ]      => intro; decompose_set_structure; fail
  end).

Ltac solve_set :=
  try_solve_set; fail.


(** ** Tactics for decidable equality 

Use [reduce_eqb] to reduce expressions of the form [x =? y] in both the hypotheses and the goal when you know either [x = y] or [x <> y].

Use [compare e1 e2] to apply decidable equality to decide whether [e1] and [e2] are equal.

Use [compare_next] to search for occurrences of [x =? y] in the context and apply [compare e1 e2].

*)
Ltac reduce_eqb :=
  repeat match goal with
  | [ H : context[ ?x =? ?x ] |- _ ] => rewrite eqb_eq in H
  | [ H : context[ ?x1 =? ?x2 ], H' : ?x1 <> ?x2 |- _] => rewrite (eqb_neq _ x1 x2) in H; [ | auto]
  | [ H : context[ ?x1 =? ?x2 ], H' : ?x2 <> ?x1 |- _] => rewrite (eqb_neq _ x1 x2) in H; [ | auto]
  | [ |- context[ ?x =? ?x ] ] => rewrite eqb_eq
  | [ H' : ?x1 <> ?x2 |- context[ ?x1 =? ?x2 ] ] => rewrite (eqb_neq _ x1 x2); [ | auto]
  | [ H' : ?x1 <> ?x2 |- context[ ?x2 =? ?x1 ] ] => rewrite (eqb_neq _ x2 x1); [ | auto]
  | [ H' : ?x1 = ?x2 |- context[ ?x1 =? ?x2 ] ] => rewrite H'
  | [ H' : ?x1 = ?x2 |- context[ ?x2 =? ?x1 ] ] => rewrite H'
  end; find_contradiction.

Ltac compare e1 e2 :=
  let Heq := fresh "Heq" in
  let Hneq := fresh "Hneq" in
  destruct (Dec e1 e2) as [Heq | Hneq]; [try subst; try (rewrite Heq) | ]; reduce_eqb.

Ltac compare_next :=
    match goal with
    | [ |- context[ eqb ?e1 ?e2 ] ] => let tp := type of e1 in
                                       compare (e1 : tp) (e2 : tp)
    | [ H : context[ eqb ?e1 ?e2 ] |- _ ] => let tp := type of e1 in compare (e1 : tp) (e2 : tp)
    end.
