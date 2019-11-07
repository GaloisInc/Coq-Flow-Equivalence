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
  Admitted.



Lemma in_flat_map_proof : forall {A B C} (a : A) (b : B) (ls : list (A*B))
                                 (f : forall a' b', In (a',b') ls -> list C)
                                 (x : C)
    (pf : In (a,b) ls),
    In x (f a b pf) ->
    In x (flat_map_proof ls f).
Admitted.

Lemma in_flat_map_proof' : forall {A B C} (ls : list (A*B))
                                 (f : forall a' b', In (a',b') ls -> list C)
                                 (x : C),
    In x (flat_map_proof ls f) ->
    exists a b (pf : In (a,b) ls), In x (f a b pf).
Admitted.

