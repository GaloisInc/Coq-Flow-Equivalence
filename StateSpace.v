Require Import Base.
Require Import FlowEquivalence.
Require Import Monad.

Section state_space.

Variable name : Set.
Context `{name_eq_dec : eq_dec name}.
Import EnsembleNotation.
Open Scope ensemble_scope.

(*Definition e_state {X} (S : Ensemble X) := forall (x : X), x ∈ S -> value.
Definition update {X} `{eq_dec X}
                  {S : Ensemble X} (σ : e_state S) (x : X) (v : value) : e_state S :=
    fun y pf_y =>
      if x =? y then v
      else σ y pf_y.
*)

Definition fin_state (X : Set) := X -> option value.
Definition fin_update {X : Set} `{eq_dec X} (σ : fin_state X) (x : X) (v : value) : fin_state X :=
  fun y => if x =? y then Some v
           else σ y.
Definition restrict {X : Set} (S : Ensemble X) `{in_dec _ S} (σ : fin_state X) : fin_state X :=
  fun y => if y ∈? S
           then σ y
           else None.
Definition in_fin_state {X} (σ : fin_state X) (x : X) :=
  match σ x with
  | Some _ => True
  | None => False
  end.


(*
Inductive e_event {X} (I O : Ensemble X) :=
| Input_Event x : x ∈ I -> value -> e_event I O
| Output_Event x : x ∈ O -> value -> e_event I O
.
Arguments Input_Event {X I O}.
Arguments Output_Event {X I O}.
Inductive is_input_event {X} {I O : Ensemble X} : option (e_event I O) -> Prop :=
| Is_Input_Event x (pf : x ∈ I) v : is_input_event (Some (Input_Event x pf v)).
Inductive event_in {X} {I O : Ensemble X} (S : Ensemble X) : option (e_event I O) -> Prop :=
| Input_Event_In x (pf : x ∈ I) v : x ∈ S -> event_in S (Some (Input_Event x pf v))
| Output_Event_In x (pf : x ∈ O) v : x ∈ S -> event_in S (Some (Output_Event x pf v))
.
*)

Inductive event :=
| Eps : event
| Value : name -> value -> event.

Inductive event_in (I : Ensemble name) : event -> Prop :=
| Event_In i (pf : i ∈ I) v : event_in I (Value i v).

Definition css_space := state name.
Definition update {X : Set} `{eq_dec X} (σ : state X) (x : X) (v : value) : state X :=
  fun y => if x =? y then v
           else σ y.


Record CircuitStateSpace :=
  { css_input : Ensemble name
  ; css_output : Ensemble name
  ; css_internal : Ensemble name
  ; css_domain := css_input ∪ css_output ∪ css_internal
  ; css_step  : css_space -> event -> option css_space -> Prop
(*
  ; css_stable := fun σ => forall e τ,
                            css_step σ e τ ->
                            event_in css_input e
*)
  }.
Notation "C ⊢ σ →{ e } τ" := (css_step C σ e τ) (no associativity, at level 70).

Record css_well_formed (S : CircuitStateSpace) (σ : css_space) :=
  { (*css_dom : forall x, x ∈ css_domain S <-> in_fin_state σ x*)
    css_input_output : css_input S ⊥ css_output S
  }.
Record css_stable (S : CircuitStateSpace) (σ : css_space) :=
  { stable_wf : css_well_formed S σ
  ; stable : forall e τ, S ⊢ σ →{e} τ -> event_in (css_input S) e }.

(*Definition CircuitStepFunction := css_space -> option e_event -> option css_space.*)

Class stable_dec (S : CircuitStateSpace) :=
  { css_stable_dec : forall σ, css_stable S σ + ~ css_stable S σ }.

Section CombStateSpace.

  (* Define a circuit state space from a combinational logic function *)

  Variable I : Ensemble name.
  Variable x : name.
  Variable f : css_space -> value.
  Hypothesis x_notin_I : ~ (x ∈ I).

  Definition comb_domain := I ∪ singleton x ∪ ∅.
  Lemma x_in_comb_domain : x ∈ comb_domain. unfold comb_domain. auto with sets. Qed.
  Lemma I_subset_comb_domain : forall i, i ∈ I -> i ∈ comb_domain.
  Proof. unfold comb_domain. auto with sets. Qed.

  Record comb_stable (σ : css_space) : Prop :=
    { comb_x_stable : σ x = f σ
(*    ; comb_I_stable : forall i, i ∈ I -> in_fin_state σ i *)
    }.
  
  Inductive comb_step (σ : css_space) :
                      event ->
                      option css_space ->
                      Prop :=
  | comb_input i (pf_i : i ∈ I) v :
    comb_stable σ ->
    σ i <> v ->
    comb_step σ (Value i v)
                (Some (update σ i v))

  | comb_err i (pf_i : i ∈ I) v :
    ~ (comb_stable σ) ->
    comb_step σ (Value i v) None

  | comb_output v :
    ~ (comb_stable σ) ->
    σ x = v ->
    comb_step σ (Value x v)
                (Some (update σ x v))
  .

(*
  Definition ERR : option css_space := None.
  Context `{in_dec _ I}.
  Definition comb_step_function (σ : css_space) (e : event) : option (option css_space) :=
    if σ x =? f σ (* comb_stable? σ *)
    then match e with
         | Some (y,v) => if y ∈? I
                         (* if the event is an input event, succeed *)
                         then Some (Some (update σ y v))
                         (* otherwise, it is an error *)
                         (* TODO: do we want to distinguish ERR from "such an event would never occur"? *)
                         else if y =? x
                         then Some ERR
                         else None
        | None => None
        end
    else match e with
         | Some (y,v) => if y ∈? I
                         (* no inputs accepted while not stable *)
                         then Some ERR
                         else if y =? x
                         then Some (Some (update σ x v))
                         else None
         | None => None
        end.
*)
    
  Program Definition comb : CircuitStateSpace :=
  {| css_input := I
   ; css_output := singleton x
   ; css_internal := ∅
   ; css_step := comb_step
   |}.

  (* This just depends on the enumerability of I *)
  Hypothesis css_wf_decidable : forall σ, css_well_formed comb σ + ~(css_well_formed comb σ).

  Lemma comb_stable_equiv : forall σ, css_well_formed comb σ ->
        comb_stable σ <-> css_stable comb σ.
  Proof.
    intros σ Hwf. split; intros Hstable.
    * (*destruct Hstable as [H_x_stable H_I_stable].*)
      split; [assumption | ].
      intros e τ Hstep.
      inversion Hstep; subst.
      + constructor. auto.
      + contradiction.
      + contradiction.
    * (*destruct Hstable as [H_stable H_I_stable].*)
      (* if the result does not hold, then we can derive a contradiction with Hstable because
         the transition on x would be enabled. *)
(*      


      destruct (σ x) as [v | ] eqn:Hv.
      2:{ absurd (in_fin_state σ x).
          + unfold in_fin_state. rewrite Hv. auto.
          + apply Hstable.
            unfold css_domain. simpl.
            auto with sets.
        }
*)
      set (v := σ x).
      compare v (f σ); auto.
      1:{ constructor; auto. }
      absurd (event_in (css_input comb) (Value x v)).
      { inversion 1; subst. simpl in *.
        contradiction. }
      { eapply Hstable.
        apply comb_output; auto.
        inversion 1.
        contradiction.
      }
  Qed.


  Instance comb_stable_dec : stable_dec comb.
  Proof.
    split.
    intros σ.
    (*
    destruct (σ x) as [v | ] eqn:Hv.
    2:{ right.
        intros [[Hwf] Hstable].
        absurd (in_fin_state σ x).
        + unfold in_fin_state.
          rewrite Hv.
          auto.
        + apply Hwf.
          unfold css_domain. simpl. auto with sets.
    }
    *)
    destruct (css_wf_decidable σ) as [Hwf | Hwf].
    2:{ right. inversion 1. contradiction. }
    {
    compare (f σ) (σ x).
    * left. apply comb_stable_equiv; auto.
      constructor; auto.

    * right. intros Hstable. 
      apply comb_stable_equiv in Hstable; auto.
      { destruct Hstable; auto.
      }
    }
  Defined.

End CombStateSpace.

Section UnionStateSpace.

  Variable S1 S2 : CircuitStateSpace.
  Hypothesis output_dec1 : in_dec (css_output S1).
  Hypothesis output_dec2 : in_dec (css_output S2).

  Hypothesis output_disjoint : css_output S1 ⊥ css_output S2.
  Hypothesis wires1_disjoint : css_internal S1 ⊥ css_domain S2.
  Hypothesis wires2_disjoint : css_domain S1 ⊥ css_internal S2.

  Let union_input := (css_input S1 ∖ css_output S2) ∪ (css_input S2 ∖ css_output S1).
  Let union_output := css_output S1 ∪ css_output S2.
  Let union_internal := css_internal S1 ∪ css_internal S2.

(*
  Program Definition e_event_coerce1
    (e : event) : 
    (e : option (e_event (css_input S1) (css_output S1))) :
    option (e_event union_input union_output) :=
    match e with
    | None => None
    | Some (Input_Event i pf v) => 
      if (i ∈? css_output S2)
      then Some (Output_Event i _ v)
      else Some (Input_Event i _ v)
    | Some (Output_Event o pf v) => Some (Output_Event o _ v)
    end.
  Next Obligation. unfold union_output. auto with sets. Qed.
  Next Obligation. unfold union_input. auto with sets. Qed.
  Next Obligation. unfold union_output. auto with sets. Qed.
  Program Definition e_event_coerce2
    (e : option (e_event (css_input S2) (css_output S2))) :
    option (e_event union_input union_output) :=
    match e with
    | None => None
    | Some (Input_Event i pf v) => 
      if (i ∈? css_output S1)
      then Some (Output_Event i _ v)
      else Some (Input_Event i _ v)
    | Some (Output_Event o pf v) => Some (Output_Event o _ v)
    end.
  Next Obligation. unfold union_output. auto with sets. Qed.
  Next Obligation. unfold union_input. auto with sets. Qed.
  Next Obligation. unfold union_output. auto with sets. Qed.
*)
  Inductive communication_event S1 S2 e :=
  | Driven1 : event_in (css_output S1) e ->
              event_in (css_input S2) e ->
              communication_event S1 S2 e
  | Driven2 : event_in (css_input S1) e ->
              event_in (css_output S2) e ->
              communication_event S1 S2 e
  | FromInput : event_in (css_input S1) e ->
                event_in (css_input S2) e ->
                communication_event S1 S2 e.

  Context `{in_dec _ (css_domain S1)} `{in_dec _ (css_domain S2)}.

  Inductive union_step (σ : css_space)
                     : event ->
                       option css_space ->
                       Prop :=
  | union_step_1 e τ :
    ~ (event_in (css_domain S2) e) ->
    S1 ⊢ σ →{e} τ ->
    (forall x2, x2 ∈ css_domain S2 -> Some (σ x2) = fmap (fun σ' => σ' x2) τ) ->
    union_step σ e τ

  | union_step_2 e τ :
    ~ (event_in (css_domain S1) e) ->
    S2 ⊢ σ →{e} τ ->
    (forall x1, x1 ∈ css_domain S1 -> Some (σ x1) = fmap (fun σ' => σ' x1) τ) ->
    union_step σ e τ

  | union_communicate e τ :
    communication_event S1 S2 e ->
    S1 ⊢ σ →{e} τ ->
    S2 ⊢ σ →{e} τ ->
    (* e must be consistent with both e1 and e2 *)
    union_step σ e τ
    .

    
  Definition ss_union : CircuitStateSpace :=
    {| css_input := union_input
     ; css_output := union_output
     ; css_internal := union_internal
     ; css_step := union_step
    |}.


  Print css_stable.

(*
  Definition stable_except (S : CircuitStateSpace) σ (X : Ensemble name) :=
    forall (e : event) τ,
      ~(event_in X e) ->
      S ⊢ σ →{e} τ ->
      event_in (css_input S) e.
  Lemma stable_implies_stable_except : forall S σ X,
    css_stable S σ -> stable_except S σ X.
  Proof.
    intros S σ X Hstable. intros e τ _ step.
    eapply Hstable; eauto.
  Qed.
*)

  Instance union_stable_dec `{stable_dec S1} `{stable_dec S2} : stable_dec ss_union.
  Proof. split.
    intros σ.
    destruct (@css_stable_dec S1 _ σ) as [stable1 | stable1];
    destruct (@css_stable_dec S2 _ σ) as [stable2 | stable2].
    
  Abort.



  Definition union_stable (σ : css_space) := 
    css_stable S1 σ /\ css_stable S2 σ.


  Lemma wf_union : forall σ,
    css_well_formed S1 σ ->
    css_well_formed S2 σ ->
    css_well_formed ss_union σ.
  Proof.
    intros σ [disjoint1] [disjoint2].
    constructor.
    simpl.
    unfold union_input, union_output.
    constructor.
    intros x Hintersect.
    inversion Hintersect as [? Hinput Houtput]; subst.
    inversion Hinput as [? Hinput1 | ? Hinput2]; subst.
    * (* x ∈ css_input S1 ∖ css_output S2 *)
      inversion Hinput1 as [Hinput1' Houtput2']; subst.
      inversion Houtput as [? Houtput1 | ? Houtput2]; subst.
      + (* contradiction, since x ∈ css_input S1 /\ x ∈ css_output S2 *)
        inversion disjoint1 as [disjoint1'].
        apply (disjoint1' x). auto with sets.
      + contradiction.
    * (* x ∈ css_input S2 ∖ css_output S1 *)
      inversion Hinput2 as [Hinput2' Houtput1']; subst.
      inversion Houtput as [? Houtput1 | ? Houtput2]; subst.
      + contradiction.
      + (* contradiction, since x ∈ css_input S1 /\ x ∈ css_output S2 *)
        inversion disjoint2 as [disjoint2'].
        apply (disjoint2' x). auto with sets.
  Qed.

  (** Note: I'm not sure the other direction actually is true, as written *)
  Lemma union_stable_implies : forall σ, 
        css_stable S1 σ ->
        css_stable S2 σ ->
        css_stable ss_union σ.
  Proof.
    intros σ Hstable1 Hstable2.
    * split; auto.
      + destruct Hstable1, Hstable2.
        apply wf_union; auto.
      + intros e τ Hstep.
           destruct Hstable1 as [Hwf1 Hstable1];
           destruct Hstable2 as [Hwf2 Hstable2].
        destruct Hstep.
        ++ assert (He : event_in (css_input S1) e).
           { eapply Hstable1; eauto. }
           inversion He; subst.
           constructor. simpl. unfold union_input.
           assert (Hi' : ~(i ∈ css_output S2)).
           { intros He'. apply H1.
             constructor. simpl. unfold css_domain. auto with sets. }
           auto with sets.
        ++ assert (He : event_in (css_input S2) e).
           { eapply Hstable2; eauto. }
           inversion He; subst.
           constructor. simpl. unfold union_input.
           assert (Hi' : ~(i ∈ css_output S1)).
           { intros He'. apply H1.
             constructor. simpl. unfold css_domain. auto with sets. }
           auto with sets.
        ++ assert (He1 : event_in (css_input S1) e).
           { eapply Hstable1; eauto. }
           assert (He2 : event_in (css_input S2) e).
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
        

End UnionStateSpace.

Section HideStateSpace.

  Variable x : name.
  Variable S : CircuitStateSpace.

  Hypothesis x_output : x ∈ css_output S.

  Let hide_input := css_input S.
  Let hide_output := css_output S ∖ singleton x.
  Let hide_internal := css_internal S ∪ singleton x.

  Inductive hide_step (σ : css_space) :
                      event ->
                      option css_space ->
                      Prop :=
  | Hide_Eq v τ:
    S ⊢ σ →{Value x v} τ ->
    hide_step σ Eps τ
  | Hide_Neq e τ :
    S ⊢ σ →{e} τ ->
    ~(event_in (singleton x) e) ->
    hide_step σ e τ
  .

  Definition ss_hide : CircuitStateSpace :=
    {| css_input := hide_input
     ; css_output := hide_output
     ; css_internal := hide_internal
     ; css_step := hide_step
    |}.


End HideStateSpace.

End state_space.

Print CircuitStateSpace.
Arguments css_input {name}.
Arguments css_output {name}.
Arguments css_internal {name}.
Arguments css_domain {name}.
Arguments css_stable {name}.
Arguments Value {name}.
Arguments Eps {name}.
Arguments comb {name}.
Notation "C ⊢ σ →{ e } τ" := (css_step _ C σ e τ) (no associativity, at level 70).
About ss_union.
Notation "S1 ∥ S2" := (ss_union _ S1 S2) (left associativity, at level 91).
