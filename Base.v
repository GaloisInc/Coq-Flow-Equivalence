Require Import Coq.Arith.PeanoNat.
Open Scope nat_scope.

Require Import Monad.
Import Notations.
Open Scope monad_scope.


Require Import List.
Import ListNotations.
Open Scope list_scope.

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

Definition in_dec' {A} `{HA : eq_dec A} : forall (a:A) l, {In a l} + {~(In a l)}.
Proof.
  apply in_dec.
  apply HA.
Defined.


  Instance prod_eq_dec {A B} `{eq_dec A} `{eq_dec B} : eq_dec (A*B).
  Proof.
    split. intros [a b] [a' b'].
    destruct (Dec a a'); destruct (Dec b b');
      subst; auto;
      right; inversion 1; contradiction.
  Defined.

  Fixpoint flat_map_proof {A B C : Type}
                          (ls : list (A*B))
                        : (forall (a : A) (b : B), In (a,b) ls -> list C)
                       -> list C :=
    match ls with
    | [] => fun _ => []
    | (a,b) :: ls' => fun f => f a b (in_eq _ _) ++ flat_map_proof ls' (fun a' b' pf' => f a' b' (in_cons _ _ _ pf'))
    end.


  Lemma flat_map_app : forall {A B} (f : A -> list B) (ls1 ls2 : list A),
    flat_map f (ls1 ++ ls2) = flat_map f ls1 ++ flat_map f ls2.
  Proof.
    intros A B f ls1. induction ls1; intros ls2.
    * reflexivity.
    * simpl. rewrite <- app_assoc. rewrite IHls1. reflexivity.
  Qed.


  Lemma in_flat_map_proof : forall {A B C} (a : A) (b : B) (ls : list (A*B))
                                   (f : forall a' b', In (a',b') ls -> list C),
    (* f is proof irrelevant *)
    (forall a' b' (pf1 pf2 : In (a',b') ls), f a' b' pf1 = f a' b' pf2) ->
    forall (x : C)
           (pf : In (a,b) ls),
           In x (f a b pf) ->
           In x (flat_map_proof ls f).
  Proof.
    intros A B C a b ls.
    induction ls as [ | c ls]; intros f f_irrel x pf pf'.
    * contradiction.
    * inversion pf; subst.
      ** simpl.
         apply in_or_app.
         left.
         rewrite (f_irrel _ _ _ pf).
         exact pf'.
      ** simpl. 
         destruct c as [a0 b0].
         apply in_or_app.
         right.
         eapply (IHls _ _ x H).
         rewrite (f_irrel _ _ _ pf).
         exact pf'.
  Unshelve. auto.
  Qed.

  Lemma in_flat_map_proof' : forall {A B C} (ls : list (A*B))
                                    (f : forall a' b', In (a',b') ls -> list C)
                                    (x : C),
    In x (flat_map_proof ls f) ->
    exists a b (pf : In (a,b) ls), In x (f a b pf).
  Proof.
    intros A B C ls.
    induction ls as [ | [a b] ls]; intros f x pf.
    * contradict pf.
    * simpl in pf.
      apply in_app_or in pf.
      destruct pf as [pf | pf].
      ** exists a, b. exists (in_eq (a,b) ls).
         exact pf.
      ** destruct (IHls _ x pf) as [a0 [b0 [pf0 IH]]].
         exists a0, b0. simpl.
         exists (in_cons (a,b) (a0,b0) ls pf0).
         exact IH.
  Qed.




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


Ltac find_contradiction :=
  try contradiction;
  try discriminate;
  try match goal with
  | [ H : ?a = _, H' : ?a = _ |- _ ] => rewrite H in H'; discriminate
  | [ H : ?a = _, H' : _ = ?a |- _ ] => rewrite H in H'; discriminate
  | [ H : _ = ?a, H' : ?a = _ |- _ ] => rewrite <- H in H'; discriminate
  | [ H : _ = ?a, H' : _ = ?a |- _ ] => rewrite H in H'; discriminate
  | [ H : ?x < ?x |- _ ] => apply Nat.lt_irrefl in H; contradiction
  end.


Ltac reduce_eqb :=
  repeat match goal with
  | [ H : context[ ?x =? ?x ] |- _ ] => rewrite eqb_eq in H
  | [ H : context[ ?x1 =? ?x2 ], H' : ?x1 <> ?x2 |- _] => rewrite eqb_neq in H; [ | auto]
  | [ H : context[ ?x1 =? ?x2 ], H' : ?x2 <> ?x1 |- _] => rewrite eqb_neq in H; [ | auto]
  | [ |- context[ ?x =? ?x ] ] => rewrite eqb_eq
  | [ H' : ?x1 <> ?x2 |- context[ ?x1 =? ?x2 ] ] => rewrite eqb_neq; [ | auto]
  | [ H' : ?x1 <> ?x2 |- context[ ?x2 =? ?x1 ] ] => rewrite eqb_neq; [ | auto]
  end; find_contradiction.

Ltac compare e1 e2 :=
  destruct (Dec e1 e2) as [? | ?]; subst; reduce_eqb.

Instance eq_dec_bool : eq_dec bool.
Proof.
  split. intros [ | ] [ | ]; try (right; inversion 1; fail); try (left; auto; fail).
Defined.


