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

  end.

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
