
Require Import Base.
Require Import Circuit.
Require Import Monad.
Require Import Setoid.
Require Import StateSpace.Definitions.
Require Import StateSpace.Tactics.
Require Import StateSpace.Reflection.

Require Import List.
Import ListNotations.
Open Scope list_scope.

Import EnsembleNotation.
Open Scope ensemble_scope.

Require Import Coq.Logic.FunctionalExtensionality.

Module FunctionalStateSpaces(Export name : NameType).
  Module Tactics := StateSpaceTactics(name).
  Export Tactics.

Class functional_step_relation (S : StateSpace name) :=
  { fun_step : state name -> option (event name value) -> Ensemble (option (state name))
  ; input_list : enumerable (space_input S)
  ; output_list : enumerable (space_output S)
  ; internal_list : enumerable (space_internal S)
  }.
Arguments fun_step S {functional_step_relation}.
Class functional_step_relation_correct (S : StateSpace name) `{functional_step_relation S} :=
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

(** Utilities *)

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
      compare_next.
      decompose_set_structure.
      specialize (IHA σ (Some σ')).
      unfold state_equiv_on in IHA.
      apply IHA; auto.
  Qed.


  Lemma equiv_on_list_equiv : forall l1 l2 σ,
    from_list l1 == from_list l2 ->
    equiv_on_list l1 σ == equiv_on_list l2 σ.
  (* proving this is trickier than I thought *)
  Admitted.
  Lemma in_list_dec_equiv : forall l1 l2 x,
    from_list l1 == from_list l2 ->
    in_list_dec x l1 = in_list_dec x l2.
  Admitted.


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

  Definition event_in_b (X : Ensemble name) `{in_dec _ X} (e : option (event name value)) :=
    match e with
    | None => false
    | Some (Event x v) => if x ∈? X then true else false
    end.


  Section FuncSpace.

  Variable I : list name.
  Variable x : name.
  Variable f : state name -> value.
  Hypothesis x_notin_I : ~ (x ∈ from_list I).


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

  Lemma func_step_in : forall σ e τ,
    func_space I x f ⊢ σ →{e} τ ->
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
      { rewrite_in_list_dec. reduce_eqb. 
        apply state_equiv_on_implies_list.
        rewrite <- Heq; auto.
      }
  Qed.


  Lemma func_in_step : forall σ e τ,
    τ ∈ func_step_fun σ e ->
    func_space I x f ⊢ σ →{e} τ.
  Proof.
    intros σ e τ Hin.
    unfold func_step_fun in Hin.
    assert (HxI : from_list I ∪ singleton x == from_list (x::I)).
    { simpl. split; intros y Hy; decompose_set_structure; solve_set. }
    destruct e as [[y v] | ]; [ | find_contradiction].
    destruct (y ∈? from_list I) as [Hy | Hy].
    { rewrite_in_list_dec.
      compare_next.
      { apply equiv_on_list_implies_state_equiv_on in Hin.
        decompose_state_equiv_on.
        apply func_input_stable; auto.
        rewrite HxI; auto.
      }
      compare_next.
      { apply equiv_on_list_implies_state_equiv_on in Hin.
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
      compare_next.
      apply equiv_on_list_implies_state_equiv_on in Hin.
      decompose_state_equiv_on.
      apply func_output; auto.
      rewrite HxI; auto.
    }
  Qed.


  Program Instance func_functional : functional_step_relation (func_space I x f) :=
    {| fun_step := func_step_fun |}.
  Instance func_functional_correct : functional_step_relation_correct (func_space I x f) :=
  {| fun_step_in := func_step_in
   ; fun_in_step := func_in_step
   |}.

  End FuncSpace.

  Section UnionStateSpace.

  Variable S1 S2 : StateSpace name.
  Hypothesis output_dec1 : in_dec (space_output S1).
  Hypothesis output_dec2 : in_dec (space_output S2).

  (** The union is only defined for two spaces that are appropriately disjoint. The spaces may share input wires with the others' output wires, however. *)

  Hypothesis output_disjoint : space_output S1 ⊥ space_output S2.
  Hypothesis wires1_disjoint : space_internal S1 ⊥ space_domain S2.
  Hypothesis wires2_disjoint : space_domain S1 ⊥ space_internal S2.

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

  Instance union_functional : functional_step_relation (S1 ∥ S2) :=
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
    (S1 ∥ S2) ⊢ σ →{e} τ -> τ ∈ union_step_fun σ e.
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
        { intro. contradict H. constructor; auto. }
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
          | [ H : union_input_event _ _ None |- _ ] => inversion H; clear H
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
    union_input_event S1 S2 (Some (Event x v)).
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
    (S1 ∥ S2) ⊢ σ →{e} τ.
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
  Instance union_functional_correct : functional_step_relation_correct (S1 ∥ S2).
  Proof.
    split.
    * apply union_implies_union_step_fun.
    * apply union_step_fun_implies_union.
  Qed.


End UnionStateSpace.

Section HideStateSpace.

  Variable x : name.
  Variable S : StateSpace name.

  Hypothesis x_output : x ∈ space_output S.

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
    hide x S ⊢ σ →{e} τ ->
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
    hide x S ⊢ σ →{e} τ.
  Proof.
    intros σ e τ Hτ. unfold hide_step_fun in Hτ.
    destruct e as [[y v] | ].
    * compare_next.
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


  Instance hide_functional : functional_step_relation (hide x S) :=
  {| fun_step := hide_step_fun |}.
    * simpl. apply input_list; auto.
    * simpl.
      set (Houtput := output_list S).
      typeclasses eauto.
    * simpl.
      set (Houtput := internal_list S).
      typeclasses eauto.
  Defined.
  Instance hide_functional_correct : functional_step_relation_correct (hide x S) :=
   {| fun_step_in := hide_fun_step_in
   ; fun_in_step := hide_fun_in_step
   |}.

End HideStateSpace.

Section Flop.

  (* the set and reset lines can be optional*)
  Variable set reset : name.
  Variable clk old_clk : name.
  Variable D Q : name.

  Context (disjoint : all_disjoint [set; reset;clk;old_clk;D;Q]).
  Let flop_input := from_list [set;reset;clk;D].
  Let flop_output := singleton Q.
  Let flop_internal := singleton old_clk.

  Let Q_output σ :=
    if σ set =? Num 0 then Num 1
    else if σ reset =? Num 0 then Num 0
    else σ D.

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
    flop set reset clk old_clk D Q ⊢ σ →{e} τ ->
    τ ∈ flop_step_fun σ e.
  Proof.
    intros σ e τ Hstep.
    destruct Hstep.
    * unfold flop_step_fun; subst.
      destruct (i ∈? flop_input); [ | find_contradiction].
      destruct H as [Hstable | Hchange].
      + destruct Hstable.
        compare_next. simpl.
        unfold update_on_flop.
        auto.
      + unfold update_on_flop. 
        repeat (compare_next; simpl; auto).

    * unfold flop_step_fun.
      destruct (i ∈? flop_input); [ | find_contradiction].
      unfold update_on_flop, update, Q_output in *.
      do 2 (compare_next; simpl; auto; try solve_set).
      contradict H.
        compare_next; simpl; auto; try solve_set.

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
    flop set reset clk old_clk D Q ⊢ σ →{e} τ.
  Proof.
    intros σ e τ Hstep.
    unfold flop_step_fun in Hstep.
    destruct e as [[x v] | ].
    2:{ compare_next.
        compare_next.
        destruct τ as [σ' | ]; [ | inversion Hstep].
        apply Flop_clk_fall; auto.
    }
    unfold update_on_flop in *.
    destruct (x ∈? flop_input); unfold flop_input in *;
    repeat (compare_next;
         simpl in Hstep;
         try decompose_state_equiv_on;
         try match goal with
         | [ |- _ ⊢ _ →{_} Some _ ] =>
           apply Flop_input; auto; fail
         | [ |- _ ⊢ _ →{_} None ] =>
           apply Flop_input_err; auto; try (inversion 1; find_contradiction); fail
         | [ Heq : ?σ set = Num 0 |- _ ] => apply Flop_set; auto; fail
         | [ Heq : ?σ reset = Num 0 |- _ ] => apply Flop_reset; auto; fail
         | [ |- _ ⊢ _ →{ Some (Event Q _) } Some _ ] => apply Flop_clk_rise; auto
         end).
    { my_subst. auto. }
  Qed.

  
  Instance flop_functional : functional_step_relation (flop set reset clk old_clk D Q) :=
  {| fun_step := flop_step_fun |}.
  Instance flop_functional_correct : functional_step_relation_correct (flop set reset clk old_clk D Q ) :=
  {| fun_step_in := flop_fun_step_in
   ; fun_in_step := flop_fun_in_step
   |}.


End Flop.

Section DelaySpace.


  Variable S : StateSpace name.
  Variable sensitivities : list name.
  (** The guard should only depend on the variables in the sensitivites set *)
  Variable guard : state name -> Prop.
  Variable guardb : state name -> bool.
  Hypothesis guardb_equiv : forall σ, guard σ <-> guardb σ = true.

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
                   (guardb σ)
      then fun_step S σ e ∩ equiv_on_list sensitivities σ
      else ∅
    end.

  Instance delay_space_functional : functional_step_relation (delay_space S sensitivities guard guardb) :=
  {| fun_step := delay_space_step_fun |}.
  * simpl. typeclasses eauto.
  * simpl. typeclasses eauto.
  Defined.

  Context `{S_functional_correct : @functional_step_relation_correct S S_functional}.
  
  Instance delay_space_functional_correct :
    functional_step_relation_correct (delay_space S sensitivities guard guardb).
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
      apply guardb_equiv in H. rewrite H.
      assert (τ ∈ fun_step S σ (Some (Event x v))) by (apply fun_step_in; auto).
      assert (τ ∈ equiv_on_list sensitivities σ).
      { apply state_equiv_on_implies_list; auto. }
      destruct (x ∈? space_input S); rewrite_in_list_dec; constructor; auto.

  * intros σ e τ Hstep.
    simpl in Hstep. unfold delay_space_step_fun in Hstep.
    destruct e as [[x v] | ].
    2:{ decompose_set_structure.
        apply delay_space_internal.
        { apply fun_in_step; auto. }
        { rewrite rewrite_enumerate.
          apply equiv_on_list_implies_state_equiv_on; auto.
        }
    }
    destruct (x ∈? space_input S); rewrite_in_list_dec.
    { decompose_set_structure.
      apply delay_space_input; auto.
      { apply fun_in_step; auto. }
      { rewrite rewrite_enumerate.
        apply equiv_on_list_implies_state_equiv_on; auto.
      }
    }
    destruct (x ∈? space_output S); rewrite_in_list_dec.
    { destruct (guardb σ) eqn:Hguard; [ simpl in Hstep | inversion Hstep].
      decompose_set_structure.
      apply delay_space_output; auto.
      { apply guardb_equiv; auto. }
      { apply fun_in_step; auto. }
      { rewrite rewrite_enumerate.
        apply equiv_on_list_implies_state_equiv_on; auto.
      }
    }
    { simpl in Hstep. find_contradiction. }
  Qed.

End DelaySpace.

Module Reflection := Structural_SS(name).
Import Reflection.

Section ISpace.

  (* NO, this doesn't work because of the non-determinism introduced by Union/Eps transitions... *)

  Notation "⊤" := (fun _ => True) : ensemble_notation.
  Open Scope ensemble_notation.


  Arguments enumerate {A} X {HX} : rename.


  Fixpoint step_ISpace (S : ISpace) (σ : state name) (e : option (event name value))
           : Ensemble (option (state name)) :=
    match S with
    | IFunc I0 x0 f0 => func_step_fun I0 x0 f0 σ e
    | IUnion S1 S2 => 
      match e with
      | Some (Event x _) =>
        if (in_list_dec x (ISpace_dom S1) && in_list_dec x (ISpace_dom S2))%bool
        then step_ISpace S1 σ e ∩ step_ISpace S2 σ e
        else if in_list_dec x (ISpace_dom S1)
        then step_ISpace S1 σ e ∩ equiv_on_list (ISpace_dom S2) σ
        else if in_list_dec x (ISpace_dom S2)
        then step_ISpace S2 σ e ∩ equiv_on_list (ISpace_dom S1) σ
        else ∅
      | None =>
        (step_ISpace S1 σ None ∩ equiv_on_list (ISpace_dom S2) σ)
     ∪ (step_ISpace S2 σ None ∩ equiv_on_list (ISpace_dom S1) σ)
      end

    | IHide x0 S0 =>
      match e with
      | Some (Event y v) => if x0 =? y then ∅ else step_ISpace S0 σ e
      | None => step_ISpace S0 σ None ∪ (fun τ => exists v, step_ISpace S0 σ (Some (Event x0 v)) τ)
      end
    | IFlop set reset clk old_clk D Q =>
      flop_step_fun set reset clk old_clk D Q σ e
    | IDelaySpace S0 sensitivities guard guardb =>
      match e with
      | Some (Event x _) =>
        if in_list_dec x (ISpace_input S0)
        then step_ISpace S0 σ e ∩ equiv_on_list sensitivities σ
        else if (in_list_dec x (ISpace_output S) && guardb σ)%bool
        then step_ISpace S0 σ e ∩ equiv_on_list sensitivities σ
        else ∅
      | None => step_ISpace S0 σ e ∩ equiv_on_list sensitivities σ
      end
    end.


  Instance ISpace_functional : forall S, functional_step_relation (interp_ISpace S).
  Proof.
    induction S; simpl.
    * apply func_functional.
    * apply union_functional; auto; typeclasses eauto.
    * apply hide_functional; auto; typeclasses eauto.
    * apply flop_functional.
    * apply delay_space_functional; auto.
  Defined.

  (*???*)
  Instance ISpace_functional_correct : forall S `{ISpace_wf S},
    functional_step_relation_correct (interp_ISpace S).
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
      destruct (guardb σ) eqn:Hguard.
      { rewrite IHS. reflexivity. }
      { reflexivity. }
  Qed.



  Theorem step_ISpace_in : forall S `{ISpace_wf S} σ e τ,
    interp_ISpace S ⊢ σ →{e} τ ->
    τ ∈ step_ISpace S σ e.
  Proof.
    intros.
    rewrite step_ISpace_correct.
    eapply fun_step_in; auto.
  Unshelve. 
    apply ISpace_functional_correct; auto.
  Qed.
  Theorem step_in_ISpace : forall S `{ISpace_wf S} σ e τ,
    τ ∈ step_ISpace S σ e ->
    interp_ISpace S ⊢ σ →{e} τ.
  Proof.
    intros S Hwf σ e τ Hτ.
    set (H := @ISpace_functional_correct S Hwf).
    rewrite step_ISpace_correct in Hτ.
    eapply fun_in_step in Hτ; auto.
  Qed.


End ISpace.
End FunctionalStateSpaces.

