Require Import Coq.Arith.PeanoNat.
Open Scope nat_scope.

Require Import Monad.
Import Notations.
Open Scope monad_scope.


Require Import List.
Import ListNotations.
Open Scope list_scope.

Require Export Coq.Sets.Ensembles.


(** * Decidable equality *)
Class eq_dec A := { Dec : forall (a b : A), {a = b} + {a <> b} }.
Definition eqb {A} `{eq_dec A} (a b : A) : bool :=
  if Dec a b then true else false.
Infix "=?" := eqb.


Lemma eqb_eq : forall A `{eq_dec A} (a : A), a =? a = true.
Proof. intros. unfold eqb. destruct (Dec a a); auto. Qed.
Lemma eqb_neq : forall A `{eq_dec A} (a b : A), a <> b -> a =? b = false.
Proof. intros. unfold eqb. destruct (Dec a b); auto. contradiction. Qed.

Fixpoint in_list_dec {A} `{eq_dec A} (a : A) (ls : list A) : bool :=
  match ls with
  | [] => false
  | b :: ls' => if a =? b then true else in_list_dec a ls'
  end.
Notation "a ∈ ls" := (in_list_dec a ls = true) (no associativity, at level 90).
Notation "a ∈? ls" := (in_list_dec a ls) (no associativity, at level 90).

Instance eq_dec_bool : eq_dec bool.
Proof.
  split. intros [ | ] [ | ]; try (right; inversion 1; fail); try (left; auto; fail).
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

(** * Snoc/tail lists *)

Inductive tail_list (A : Type) :=
| t_empty : tail_list A
| t_next : tail_list A -> A -> tail_list A.
Arguments t_empty {A}.
Arguments t_next {A}.
Infix "▶" := t_next (left associativity, at level 73).



(** ** Ensemble notation *)
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

Open Scope ensemble_scope.
Class in_dec {Z} (X : Ensemble Z) := {In_Dec : forall (x:Z), {x ∈ X} + {~(x ∈ X)}}.
Notation "x ∈? X" := (@In_Dec _ X _ x) : ensemble_scope.

Lemma Setminus_in : forall {A} x (X Y : Ensemble A),
    x ∈ X ∖ Y ->
    (x ∈ X).
Admitted.
Lemma Setminus_not_in : forall {A} x (X Y : Ensemble A),
    x ∈ X ∖ Y ->
    ~(x ∈ Y).
Admitted.
Hint Resolve Setminus_in Setminus_not_in : sets.

Lemma not_union_1 : forall {A} (x : A) X Y,
    ~(x ∈ X ∪ Y) ->
    ~(x ∈ X).
Admitted.
Lemma not_union_2 : forall {A} (x : A) X Y,
    ~(x ∈ X ∪ Y) ->
    ~(x ∈ X).
Admitted.
Hint Resolve not_union_1 not_union_2 : sets.
  Fixpoint from_list {A} (l : list A) : Ensemble A :=
    match l with
    | nil => ∅
    | x :: l' => singleton x ∪ from_list l'
    end.

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
  end.



Ltac decompose_set_structure :=
  repeat (match goal with
  | [ H : ?x ∉ ∅ |- _ ] => clear H
  | [ H : ?x ∈ ?X ∖ ?Y |- _ ] => destruct H 
  | [ H : ?x ∈ ?X ∪ ?Y |- _ ] => inversion H; subst; clear H
  | [ H : ?x ∈ ?X ∩ ?Y |- _ ] => inversion H; subst; clear H
  | [ H : ~(?x ∈ ?X ∪ ?Y) |- _] => assert (~(x ∈ X)) by auto with sets;
                                   assert (~(x ∈ Y)) by auto with sets;
                                   clear H
  | [ H : ?x ∉ singleton ?y |- _ ] => apply not_in_singleton_neq in H
  | [ H : ?x ∈ Couple _ ?y ?z |- _] => inversion H; subst; clear H
  | [ H : ?x ∈ singleton ?y |- _ ] => inversion H; subst; clear H
  | [ H : all_disjoint [] |- _ ] => clear H
  | [ H : all_disjoint (_ :: _) |- _] => let H' := fresh "H" in
                                         inversion H as [ | ? ? H']; subst; 
                                         simpl in H'; clear H
  end; try find_contradiction; auto with sets).

Ltac solve_set :=
  repeat (auto with sets;
  match goal with
  | [ |- ?x ∉ singleton ?y ] => apply not_in_singleton_neq
  | [ |- ?x ∈ ?X ∖ ?Y ] => constructor
  | [ |- ?x ∈ ?X ∪ ?Y ] => left; solve_set; fail
  | [ |- ?x ∈ ?X ∪ ?Y ] => right; solve_set; fail
  | [ |- ?x ∈ ?X ∩ ?Y ] => constructor
  end).
(** ** Decidable equality *)
Ltac reduce_eqb :=
  repeat match goal with
  | [ H : context[ ?x =? ?x ] |- _ ] => rewrite eqb_eq in H
  | [ H : context[ ?x1 =? ?x2 ], H' : ?x1 <> ?x2 |- _] => rewrite (eqb_neq _ x1 x2) in H; [ | auto]
  | [ H : context[ ?x1 =? ?x2 ], H' : ?x2 <> ?x1 |- _] => rewrite (eqb_neq _ x1 x2) in H; [ | auto]
  | [ |- context[ ?x =? ?x ] ] => rewrite eqb_eq
  | [ H' : ?x1 <> ?x2 |- context[ ?x1 =? ?x2 ] ] => rewrite (eqb_neq _ x1 x2); [ | auto]
  | [ H' : ?x1 <> ?x2 |- context[ ?x2 =? ?x1 ] ] => rewrite (eqb_neq _ x2 x1); [ | auto]
  end; find_contradiction.

Ltac compare e1 e2 :=
  destruct (Dec e1 e2) as [? | ?]; subst; reduce_eqb.

Ltac compare_next :=
    match goal with
    | [ |- context[ eqb ?e1 ?e2 ] ] => let tp := type of e1 in
                                       compare (e1 : tp) (e2 : tp)
    | [ H : context[ eqb ?e1 ?e2 ] |- _ ] => let tp := type of e1 in compare (e1 : tp) (e2 : tp)
    end.
