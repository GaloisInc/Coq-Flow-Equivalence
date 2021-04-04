Require Import Base.
Require Import Circuit.
Require Import Monad.
Require Import Setoid.

Require Import StateSpace.Definitions.
Require Import StateSpace.Tactics.

Require Import Program.Equality.

Require Import List.
Import ListNotations.
Open Scope list_scope.

Import EnsembleNotation.
Open Scope ensemble_scope.
Require Import FunctionalExtensionality.




Module Structural_SS (Export name : NameType).

  Inductive ISpace :=
  | IFunc (I : list name) (x : name) (f : state name -> value) : ISpace
  | IUnion (S1 S2 : ISpace) : ISpace
  | IHide  (x : name) (S : ISpace) : ISpace
  | IFlop (set reset clk old_clk D Q : name) : 
    (*all_disjoint [set;reset;clk;old_clk;D;Q] ->*)
    ISpace
  | IDelaySpace (S : ISpace)
                (sensitivities : list name)
                (guard : state name -> Prop)
                (guardb : state name -> bool) : ISpace
(*  | IPrim : StateSpace name -> ISpace*)
  .

  Fixpoint interp_ISpace (S : ISpace) : StateSpace name :=
    match S with
(*    | IPrim S0     => S0*)
    | IFunc I' x f  => func_space I' x f
    | IUnion S1 S2 => interp_ISpace S1 ∥ interp_ISpace S2
    | IHide x S0   => hide x (interp_ISpace S0)
    | IFlop set reset clk old_clk D Q => flop set reset clk old_clk D Q
    | IDelaySpace S0 sens guard guardb => delay_space (interp_ISpace S0) sens guard guardb
    end.

  Fixpoint ISpace_dom (S : ISpace) : list name :=
    match S with
    | IFunc I0 x0 f0 => x0 :: I0
    | IUnion S1 S2 => ISpace_dom S1 ++ ISpace_dom S2
    | IHide x0 S0  => x0 :: ISpace_dom S0 (* Adding the x0 lets us prove
                                             correctness of ISpace_dom without
                                             well-formedness *)
    | IFlop set reset clk old_clk D Q => set::reset::clk::old_clk::D::Q::nil
    | IDelaySpace S0 sens guard guardb => ISpace_dom S0 ++ sens
    end.

  Fixpoint ISpace_output (S : ISpace) : list name :=
    match S with
    | IFunc I0 x0 f0 => x0 :: nil
    | IUnion S1 S2 => ISpace_output S1 ++ ISpace_output S2
    | IHide x0 S0  => better_filter (fun y => negb (x0 =? y)) (ISpace_output S0)
                      (*list_setminus (ISpace_output S0) (x0::nil)*)
    | IFlop set reset clk old_clk D Q => Q::nil
    | IDelaySpace S0 sens guard guardb => ISpace_output S0
    end.

  Fixpoint ISpace_input (S : ISpace) : list name :=
    match S with
    | IFunc I0 x0 f0 => I0
    | IUnion S1 S2 => list_setminus (ISpace_input S1) (ISpace_output S2)
                   ++ list_setminus (ISpace_input S2) (ISpace_output S1)
    | IHide x0 S0  => ISpace_input S0
    | IFlop set reset clk old_clk D Q => set::reset::clk::D::nil
    | IDelaySpace S0 sens guard guardb => ISpace_input S0 ++ sens
    end.

  Fixpoint ISpace_internal (S : ISpace) : list name :=
    match S with
    | IFunc I0 x0 f0 => nil
    | IUnion S1 S2 => ISpace_internal S1 ++ ISpace_internal S2
    | IHide x0 S0  => x0 :: ISpace_internal S0
    | IFlop set reset clk old_clk D Q => old_clk::nil
    | IDelaySpace S0 sens guard guardb => ISpace_internal S0
    end.

  Lemma setminus_singleton_equiv : forall x (l : list name),
    from_list (better_filter (fun y => negb (x =? y)) l)
    == from_list l ∖ singleton x.
  Proof.
    intros x l.
    setoid_replace (singleton x) with (from_list [x]).
    2:{ split; intros y Hy; decompose_set_structure; solve_set. }
    rewrite <- list_setminus_equiv.
    unfold list_setminus.

    replace (fun y => negb (x =? y))
      with  (fun y => negb (in_list_dec y [x])).
    2:{ apply functional_extensionality.
        intros y. simpl.
        compare x y; auto.
      }
    reflexivity.
  Qed.




  Lemma space_output_ISpace : forall S,
    space_output (interp_ISpace S) == from_list (ISpace_output S).
  Proof.
    induction S; simpl.
    * rewrite union_emptyset_r. reflexivity.
    * rewrite from_list_app.
      rewrite IHS1, IHS2.
      reflexivity.
    * rewrite IHS.
      rewrite setminus_singleton_equiv.
      reflexivity.
    * rewrite union_emptyset_r. reflexivity.
    * auto.
  Qed.

  Lemma space_input_ISpace : forall S,
    space_input (interp_ISpace S) == from_list (ISpace_input S).
  Proof.
    induction S; simpl.
    * reflexivity.
    * rewrite IHS1, IHS2.
      repeat rewrite space_output_ISpace.
      rewrite from_list_app.

      apply union_mor.
      + rewrite list_setminus_equiv.
        reflexivity.
      + rewrite list_setminus_equiv.
        reflexivity.
    * auto.
    * reflexivity.
    * rewrite IHS.
      rewrite from_list_app.
      reflexivity.
  Qed.
  Lemma space_internal_ISpace : forall S,
    space_internal (interp_ISpace S) == from_list (ISpace_internal S).
  Proof.
    induction S; simpl.
    * reflexivity.
    * rewrite IHS1, IHS2.
      rewrite from_list_app.
      reflexivity.
    * rewrite IHS.
      apply union_symm.
    * rewrite union_emptyset_r. reflexivity.
    * auto.
  Qed.



  Lemma space_domain_ISpace_union : forall S,
    from_list (ISpace_dom S)
    == from_list (ISpace_input S) ∪ from_list (ISpace_output S) ∪ from_list (ISpace_internal S).
  Proof.
    induction S; simpl.
    * repeat rewrite union_emptyset_r.
      apply union_symm.

    * repeat rewrite from_list_app.
      repeat rewrite list_setminus_equiv.
      rewrite IHS1, IHS2.
          
      remember (from_list (ISpace_input S1)) as A1.
      remember (from_list (ISpace_input S2)) as A2.
      remember (from_list (ISpace_output S1)) as B1.
      remember (from_list (ISpace_output S2)) as B2.
      assert (B1dec : in_dec B1). { subst. apply from_list_in_dec. }
      assert (B2dec : in_dec B2). { subst. apply from_list_in_dec. }
      remember (from_list (ISpace_internal S1)) as C1.
      remember (from_list (ISpace_internal S2)) as C2.
      clear S1 HeqA1 HeqB1 HeqC1 IHS1.
      clear S2 HeqA2 HeqB2 HeqC2 IHS2.
      
      transitivity (((A1 ∖ B2) ∪ B2) ∪ ((A2 ∖ B1) ∪ B1) ∪ C1 ∪ C2).
      2:{ (* just commutativity of ∪ *)
          remember (A1 ∖ B2) as D1.
          remember (A2 ∖ B1) as D2.
          clear A1 A2 HeqD1 HeqD2.
          split; intros x Hx; decompose_set_structure.
      }
      transitivity ((A1 ∪ B2) ∪ (A2 ∪ B1) ∪ C1 ∪ C2).
      { (* just commutativity of ∪ *)
          split; intros x Hx; decompose_set_structure.
      }
      repeat rewrite setminus_union_equiv; auto.
      reflexivity.

    * (* hide *)
      rewrite IHS.
      rewrite setminus_singleton_equiv.

      remember (from_list (ISpace_input S)) as A.
      remember (from_list (ISpace_output S)) as B.
      remember (from_list (ISpace_internal S)) as C.
      remember (singleton x) as D.
      assert (Ddec : in_dec D). { subst. apply in_dec_singleton. }
      clear S HeqA HeqB HeqC HeqD IHS.
      
      transitivity (A ∪ (B ∪ D) ∪ C).
      { (* commutativity *)
        split; intros ? ?; decompose_set_structure.
      }
      rewrite <- (setminus_union_equiv B D).
      remember (B ∖ D) as E.
      clear B HeqE.

      split; intros ? ?; decompose_set_structure.

    * (* flop *)
      split; intros ? ?; decompose_set_structure; solve_set.
    * (* delay_space *)
      repeat rewrite from_list_app.
      rewrite IHS.
      split; intros ? ?; decompose_set_structure.
  Qed.


  Lemma space_domain_ISpace : forall S,
    space_domain (interp_ISpace S) == from_list (ISpace_dom S).
  Proof.
    intros. rewrite space_domain_ISpace_union.
    unfold space_domain.
    rewrite space_output_ISpace.
    rewrite space_input_ISpace.
    rewrite space_internal_ISpace.
    reflexivity.
  Qed.


  Inductive ISpace_wf : ISpace -> Prop :=
  | IFunc_wf : forall I x f,
    x ∉ from_list I ->
    ISpace_wf (IFunc I x f)
  | IUnion_wf S1 S2 :
    list_intersection (ISpace_internal S1) (ISpace_dom S2) = nil ->
    list_intersection (ISpace_internal S2) (ISpace_dom S1) = nil ->
    ISpace_wf S1 ->
    ISpace_wf S2 ->
    ISpace_wf (IUnion S1 S2)
  (* more... *)
  .
  

  Lemma interp_ISpace_wf : forall S,
    ISpace_wf S ->
    well_formed (interp_ISpace S).
  Abort.






  Ltac reflect_ISpace S :=
  match S with
  | func_space ?I0 ?x ?f => constr:(IFunc I0 x f)
  | ?S1 ∥ ?S2            => let SS1 := reflect_ISpace S1 in
                            let SS2 := reflect_ISpace S2 in
                            constr:(IUnion SS1 SS2)
  | hide ?x ?S'          => let SSS' := reflect_ISpace S' in
                            constr:(IHide x SSS')
  | flop ?set ?reset ?clk ?old_clk ?D ?Q => constr:(IFlop set reset clk old_clk D Q)
  | delay_space ?S0 ?sens ?guard  ?guardb    => let SS := reflect_ISpace S0 in
                                      constr:(IDelaySpace SS sens guard guardb)
(*  | _                              => constr:(IPrim S)*)
  end.
  Ltac reflect_S S := 
    let S' := reflect_ISpace S in
    replace S with (interp_ISpace S') by reflexivity.
  Module SSTactics := StateSpaceTactics(name).
  Import SSTactics.

  Ltac reflect_StateSpace :=
  match goal with
  | [ |- ?S1 = ?S2 ] => unfold_StateSpace S1;
                        unfold_StateSpace S2;
    match goal with
    | [ |- ?S1' = ?S2' ] => reflect_S S1'; reflect_S S2'
    end
  end.

(* Currently do not support C_elem
  Section Test.
  Variable x : name.
  Let S : StateSpace name := C_elem x x x.
  Let S' := (S ∥ func_space (x::nil) x (fun _ => X)).
  Lemma foo : S' = S.
    assert (Heq : S' = S') by reflexivity.
    unfold_StateSpace S' in Heq.
    reflect_StateSpace.
  Abort.
  End Test.
*)


  Definition update_oevent (σ : state name) (e : option (event name value)) : state name :=
    match e with
    | None => σ
    | Some (Event x v) => update σ x v
    end.



 (* Set reflection, with ISpaces built in  *)

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
                        constr:(SetSpaceInput S0')
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
  | SetIntersection S1 S2 => list_intersection (SetStructure_to_list S1)
                                               (SetStructure_to_list S2)
  | SetDifference S1 S2 => list_setminus  (SetStructure_to_list S1)
                                          (SetStructure_to_list S2)
  | SetSpaceDomain S0 => ISpace_dom S0
  | SetSpaceInput S0 => ISpace_input S0
  | SetSpaceOutput S0 => ISpace_output S0
  | SetSpaceInternal S0 => ISpace_internal S0
  end.


  Lemma SetStructure_to_list_correct : forall S,
    interpret_SetStructure S == from_list (SetStructure_to_list S).
  Proof.
    induction S; simpl; try reflexivity.
    * rewrite union_emptyset_r. reflexivity.
    * rewrite from_list_app.
      rewrite IHS1, IHS2.
      reflexivity.
    * rewrite list_intersection_equiv.
      rewrite IHS1, IHS2.
      reflexivity.
    * rewrite list_setminus_equiv.
      rewrite IHS1, IHS2.
      reflexivity.
    * apply space_domain_ISpace.
    * apply space_input_ISpace.
    * apply space_output_ISpace.
    * apply space_internal_ISpace.
  Qed.

  Ltac set_to_list HS S :=
    let S0 := reflect_to_SetStructure S in
    let l0 := eval simpl in (SetStructure_to_list S0) in
    assert (HS : S == from_list l0);
    [ transitivity (interpret_SetStructure S0);
      [ reflexivity | rewrite SetStructure_to_list_correct; reflexivity]
    | ].

  (** * Solve goal of the form x ∈ S or x ∉ S by reflection. *)
  Ltac solve_space_set :=
  match goal with
  | [ |- ?x ∈ ?S ] => let H := fresh "H" in
                      set_to_list H S; rewrite H; clear H;
                      to_in_list_dec; unfold in_list_dec; reduce_eqb; auto;
                      simpl; reduce_eqb; auto
  | [ |- ?x ∉ ?S ] => let H := fresh "H" in
                      set_to_list H S; rewrite H; clear H;
                      to_in_list_dec; unfold in_list_dec; reduce_eqb; auto;
                      simpl; reduce_eqb; auto
  end.


  Ltac space_domain_to_list Hdom S :=
  let l := fresh "l" in
  evar (l : list name);
  assert (Hdom : space_domain S == from_list l);
  [ unfold_StateSpace S;
    match goal with
    | [ |- space_domain ?S == _ ] => let S' := reflect_ISpace S in
                                     transitivity (space_domain (interp_ISpace S'));
                                     [ reflexivity | ]
    end;
    rewrite space_domain_ISpace;
    unfold l;
    reflexivity
  | simpl in l;
    unfold l in Hdom;
    clear l
    ].


  Ltac compare_next_in_list_dec :=
  match goal with
  | [ Hstep : ?S ⊢ _ →{Some (Event ?x _)} _
    |- context[ in_list_dec ?x (enumerate (space_domain ?S) _) ] ]=>
    let Hdom := fresh "Hdom" in
    space_domain_to_list Hdom S;
    rewrite Hdom;
    rewrite <- rewrite_enumerate

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



End Structural_SS.
