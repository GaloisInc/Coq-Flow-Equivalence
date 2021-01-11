Require Import Base.
Require Import Circuit.
Require Import Monad.
Require Import Setoid.

Require Import StateSpace.Definitions.

Require Import List.
Import ListNotations.
Open Scope list_scope.

Import EnsembleNotation.
Open Scope ensemble_scope.

Module Type NameType.
  Parameter name : Set.
  Parameter name_eq_dec : eq_dec name.
  Existing Instance name_eq_dec.
  Export EnsembleNotation.
  Open Scope ensemble_scope.

End NameType.

Module StateSpaceTactics (Export name : NameType).

  Add Parametric Morphism : event_in
    with signature Same_set name ==> @eq (option (event name value)) ==> iff as event_in_equiv.
  Proof.
    intros.
    apply event_in_equiv; auto.
  Qed.
  Add Parametric Morphism : state_equiv_on
    with signature (Same_set name) ==> (@eq (option (state name)))
                                   ==> (@eq (option (state name))) ==> iff
    as state_equiv_on_equiv.
  Proof.
    intros.
    apply state_equiv_on_equiv; auto.
  Qed.

  Ltac rewrite_state_equiv :=
  match goal with
  | [ H : state_equiv_on ?X (Some ?σ') (Some _) |- context[?σ' _] ] =>
    rewrite H; [ try unfold update | decompose_set_structure]
  | [ H : state_equiv_on ?X (Some _) (Some ?σ') |- context[?σ' _] ] =>
    rewrite <- H; [ try unfold update | decompose_set_structure]
  end.


  Ltac rewrite_state_equiv_branch y :=
  match goal with
  | [ Hequiv : state_equiv_on ?X (Some ?σ) (Some ?σ')
    |- context[ ?σ' y ] ] =>
      let Hy := fresh "Hy" in
      destruct (y ∈? X) as [Hy | Hy];
        [ rewrite_state_equiv | clear Hequiv]
  end.


  Lemma union_inversion_left : forall (S1 S2 : StateSpace name) σ x v σ',
    (S1 ∥ S2) ⊢ σ →{Some (Event x v)} Some σ' ->
    x ∈ space_domain S1 ->
    S1 ⊢ σ →{Some (Event x v)} Some σ'.
  Proof.
    intros ? ? ? ? ? ? Hstep Hdom.
    inversion Hstep; subst; auto.
    (* the only remaining case is when x ∉ dom(S1), a contradiction *)
    { absurd (event_in (space_domain S1) (Some (Event x v))); auto.
      constructor; auto.
    }
  Qed.

  Lemma union_inversion_left_only : forall (S1 S2 : StateSpace name) σ e σ',
    (S1 ∥ S2) ⊢ σ →{e} Some σ' ->
    event_in (space_domain S1) e ->
    ~ event_in (space_domain S2) e ->
    S1 ⊢ σ →{e} Some σ'
    /\ state_equiv_on (space_domain S2) (Some σ) (Some σ').
  Proof.
    intros ? ? ? ? ? Hstep H1 H2.
    inversion Hstep; subst; split; auto; 
      try contradiction.
    contradict H2.
    inversion H; subst; auto;
    match goal with
    [ H : event_in (_ ?S2) ?e |- event_in (space_domain ?S2) ?e ] =>
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
    { absurd (event_in (space_domain S2) (Some (Event x v))); auto.
      constructor; auto.
    }
  Qed.

  Lemma union_inversion_right_only : forall (S1 S2 : StateSpace name) σ e σ',
    (S1 ∥ S2) ⊢ σ →{e} Some σ' ->
    ~ event_in (space_domain S1) e ->
    event_in (space_domain S2) e ->
    S2 ⊢ σ →{e} Some σ'
    /\ state_equiv_on (space_domain S1) (Some σ) (Some σ').
  Proof.
    intros ? ? ? ? ? Hstep H1 H2.
    inversion Hstep; subst; split; auto; 
      try contradiction.
    contradict H1.
    inversion H; subst; auto;
    match goal with
    [ H : event_in (_ ?S2) ?e |- event_in (space_domain ?S2) ?e ] =>
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

  Lemma union_inversion_None : forall (S1 S2 : StateSpace name) σ σ',
    (S1 ∥ S2) ⊢ σ →{None} Some σ' ->
       (S1 ⊢ σ →{None} Some σ' /\ state_equiv_on (space_domain S2) (Some σ) (Some σ'))
    \/ (S2 ⊢ σ →{None} Some σ' /\ state_equiv_on (space_domain S1) (Some σ) (Some σ')).
  Proof.
    intros S1 S2 σ σ' Hstep.
    inversion Hstep; subst; auto.
    inversion H;
    match goal with
    | [ H : event_in _ None |- _ ] => inversion H
    end.
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
    inversion Hstep; subst;
    match goal with
    | [ H : state_equiv_on _ _ (Some ?σ') |- ?σ' _ = _ ] => rewrite <- H;
      [unfold update | try solve_set]
    end;
      compare_next; auto.
  Qed.

  Lemma func_space_inversion_None : forall I (o : name) f (σ : state name) σ',
      func_space I o f ⊢ σ →{None} Some σ' ->
      False.
  Proof.
    intros. inversion H.
  Qed.

Lemma func_space_inversion : forall I o f σ e σ',
  o ∉ from_list I ->
  func_space I o f ⊢ σ →{e} Some σ' ->
  match e with
  | None => False
  | Some (Event y v) => state_equiv_on (from_list I ∪ singleton o) (Some (update σ y v)) (Some σ')
                    /\ (y = o -> (v = f σ /\ f σ <> σ o))
                    /\ (y ∈ from_list I -> f σ = σ o \/ f σ = f (update σ y v))
  end.
Proof.
  intros ? ? ? ? ? ? Hwf Hstep.
  inversion Hstep; subst.
  * split; auto. split; auto.
    intro Hi; subst; find_contradiction.
  * split; auto. split; auto.
    { intros Heq; subst; find_contradiction. }
  * split; auto. split; auto.
    { intros Hin. find_contradiction. }
Qed.

  Lemma flop_inversion_output : forall set reset clk old_clk D Q σ v σ',
    all_disjoint [set; reset;clk;old_clk;D;Q] ->
    σ set = Bit1 ->
    σ reset = Bit1 ->
    flop set reset clk old_clk D Q ⊢ σ →{Some (Event Q v)} Some σ' ->
    σ clk = Bit1 /\
    σ old_clk <> Bit1 /\
    v = σ D /\
     state_equiv_on (from_list [set;reset;clk;D;Q;old_clk])
        (Some (update (update σ Q v) old_clk (σ clk)))
        (Some σ').
  Proof.
    intros ? ? ? ? ? ? ? ? ? ? Hset Hreset Hstep.
    inversion Hstep; subst; auto; clear Hstep.
    + contradict H5. simpl. solve_set.
    + find_contradiction.
    + find_contradiction.
  Qed.


  Lemma flop_inversion_clk : forall set reset clk old_clk D Q σ v σ',
    all_disjoint [set;reset;clk;old_clk;D;Q] ->
    (flop set reset clk old_clk D Q) ⊢ σ →{Some (Event clk v)} Some σ' ->
    σ set = Bit1 ->
    σ reset = Bit1 ->
    state_equiv_on (from_list (set::reset::clk::D::Q::old_clk::nil)) (Some (update σ clk v)) (Some σ')
    /\ σ clk = σ old_clk.
  Proof.
    intros ? ? ? ? ? ? ? ? ? Hdisjoint Hstep Hset Hreset.
    inversion Hstep; try (subst; find_contradiction; fail).
    * split; auto.
  Qed.


Ltac unfold_SS recurse_flag loc_flag S :=
  match S with

  | func_space ?I0 ?x ?f => idtac
  | ?S1 ∥ ?S2            =>
    (* If the recurse_flag is true then we want to unfold recursively; if false,
    only unfold the head term, in this case, already a Union *)
    maybe_do recurse_flag ltac:(unfold_SS recurse_flag loc_flag S1);
    maybe_do recurse_flag ltac:(unfold_SS recurse_flag loc_flag S2)
  | hide ?x ?S'          =>
    maybe_do recurse_flag ltac:(unfold_SS recurse_flag loc_flag S')
  | flop ?set ?reset ?clk ?old_clk ?D ?Q => idtac
  | delay_space ?S0 ?sens ?guard ?guardb    => 
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
         let guardb := fresh "guardb" in
         evar (S0 : StateSpace name);
         evar (sens : list name);
         evar (guard : state name -> Prop);
         evar (guardb : state name -> bool);
         replace_with_in S (delay_space S0 sens guard guardb) loc_flag;
         unfold S0, sens, guard, guardb in *;
         [ | reflexivity];
         maybe_do recurse_flag ltac:(let S0' := eval unfold S0 in S0 in
                                unfold_SS recurse_flag loc_flag S0');
         clear S0 sens guard guardb
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

End StateSpaceTactics.
