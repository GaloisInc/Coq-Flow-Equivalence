Require Import Base.
Require Import FlowEquivalence.
Require Import StateSpace.
Require Import Monad.

Section Click.

Variable name : Set.
Context `{eq_dec name}.
Import EnsembleNotation.
Open Scope ensemble_scope.


Section Flop.

  Variable dp_reset : name.
  Variable clk old_clk : name.
  Variable state0 : name.
  Variable reset_value : value (* the value to set state0 when dp_reset=0 *).
  Hypothesis dp_reset_neq_clk : dp_reset <> clk.
  Hypothesis dp_reset_neq_state0 : dp_reset <> state0.
  Hypothesis clk_neq_state0 : clk <> state0.
  Let flop_input := Couple _ dp_reset clk.
  Let flop_output := singleton state0.
  Let flop_internal := singleton old_clk.

  Let flop_stable σ := (σ dp_reset = Num 0 -> σ state0 = Num 0)
                    /\ (σ dp_reset = Num 1 -> σ clk = σ old_clk).


  Definition neg_value (v : value) : value :=
    match v with 
    | Num 0 => Num 1
    | Num 1 => Num 0
    | _ => v
    end.

  Inductive flop_step (σ : css_space name) :
                      event name ->
                      option (css_space name) ->
                      Prop :=
  | Flop_Input_Stable i v :
    flop_stable σ ->
    i ∈ flop_input ->
    σ i <> v ->
    flop_step σ (Value i v) (Some (update σ i v))

  | Flop_Input_Unstable i v :
    ~ flop_stable σ ->
    i ∈ flop_input ->
    flop_step σ (Value i v) None

  | Flop_Reset :
    ~ flop_stable σ ->
    σ dp_reset = Num 0 ->
    flop_step σ (Value state0 reset_value) (Some (update σ state0 reset_value))

  | Flop_clk1 new_state0 :
    ~ flop_stable σ ->
    σ dp_reset = Num 1 ->
    σ clk = Num 1 ->
    new_state0 = neg_value (σ state0) ->
    flop_step σ (Value state0 new_state0) (Some (update (update σ state0 new_state0) old_clk (Num 1)))

  | Flop_clk0 :
    ~ flop_stable σ ->
    σ dp_reset = Num 1 ->
    σ clk <> Num 1 ->
    flop_step σ Eps (Some (update σ old_clk (σ clk)))
  .


  Definition flop : CircuitStateSpace name :=
    {| css_input := flop_input
     ; css_output := flop_output
     ; css_internal := flop_internal
     ; css_step := flop_step
    |}.

  Lemma flop_stable_implies_stable : forall σ, 
    flop_stable σ -> css_stable flop σ.
  Proof.
    intros σ Hstable.
    constructor.
    * (* well-formed *)
      constructor.
      constructor.
      intros x Hx.
      inversion Hx as [? Hx_input Hx_output]; subst.
      simpl in *. unfold flop_input in *; unfold flop_output in *.
      inversion Hx_output; subst.
      inversion Hx_input; subst;
      contradiction.
    * intros e τ Hstep.
      destruct Hstep;
        try contradiction;
        try (constructor; auto; fail).
  Qed.

  Lemma stable_implies_flop_stable : forall σ,
    css_stable flop σ ->
    flop_stable σ.
  Proof.
    intros σ Hstable. constructor; intros Hdp_reset.
    + (* dp_reset = 0 *)
      compare (σ state0) (Num 0); auto.
      (* derive a contradiction, since we can have σ -> σ[state0 ↦ 0] *)
      assert (Hstep : flop ⊢ σ →{Value state0 reset_value} Some (update σ state0 reset_value)).
      { apply Flop_Reset; auto.
        intros [Hreset0 _].
        specialize (Hreset0 Hdp_reset).
        contradiction.
      }
      destruct Hstable as [_ Hstable].
      specialize (Hstable _ _ Hstep).
      contradict Hstable.
      inversion 1; subst. simpl in pf. inversion pf; contradiction.
    + (* dp_reset = 1 *)
      compare (σ clk) (σ old_clk); auto.
      (* derive a contradiction, since σ is no longer flop_stable *)
      assert (Hstable' : ~ flop_stable σ).
      { intros [Hreset0 Hreset1].
        specialize (Hreset1 Hdp_reset).
        contradiction.
      }
      compare (σ clk) (Num 1).
      { assert (Hstep : flop ⊢ σ →{Value state0 (neg_value (σ state0))}
                                  Some (update (update σ state0 (neg_value (σ state0))) old_clk (Num 1))).
        { eapply Flop_clk1; auto. }
        destruct Hstable as [_ Hstable].
        specialize (Hstable _ _ Hstep).
        contradict Hstable.
        inversion 1; subst. simpl in pf. inversion pf; contradiction.
      }
      { assert (Hstep : flop ⊢ σ →{Eps} (Some (update σ old_clk (σ clk)))).
        { eapply Flop_clk0; auto. }
        
        destruct Hstable as [_ Hstable].
        specialize (Hstable _ _ Hstep).
        contradict Hstable.
        inversion 1; subst.
      }
  Qed.

End Flop.

Section Celem.

  Variable x1 x2 y : name.
  Let C_input := Couple _ x1 x2.
  Let C_output := singleton y.
  
  Let C_stable σ := (σ x1 = Num 0 /\ σ x2 = Num 0 -> σ y = Num 0)
                 /\ (σ x1 = Num 1 /\ σ x2 = Num 1 -> σ y = Num 1).

  Inductive C_step (σ : css_space name) :
                      event name ->
                      option (css_space name) ->
                      Prop :=
  | C_input1_stable v :
    C_stable σ ->
    σ x1 <> v ->
    C_step σ (Value x1 v) (Some (update σ x1 v))
  | C_input2_stable v :
    C_stable σ ->
    σ x2 <> v ->
    C_step σ (Value x2 v) (Some (update σ x2 v))


  | C_input1_unstable v :
    ~ C_stable σ ->
    σ x1 <> v ->
    C_step σ (Value x1 v) None
  | C_input2_unstable v :
    ~ C_stable σ ->
    σ x2 <> v ->
    C_step σ (Value x2 v) None

  | C_output0 :
    σ x1 = Num 0 ->
    σ x2 = Num 0 ->
    σ y <> Num 0 ->
    C_step σ (Value y (Num 0)) (Some (update σ y (Num 0)))
  | C_output1 :
    σ x1 = Num 1 ->
    σ x2 = Num 1 ->
    σ y <> Num 1 ->
    C_step σ (Value y (Num 1)) (Some (update σ y (Num 1)))
  .

  Definition ss_C : CircuitStateSpace name :=
    {| css_input := C_input
     ; css_output := C_output
     ; css_internal := ∅
     ; css_step := C_step
    |}.

  Lemma C_stable_implies_stable : forall σ, C_stable σ -> css_stable ss_C σ.
  Abort.
  Lemma stable_implies_C_stable : forall σ, css_stable ss_C σ -> C_stable σ.
  Abort.

End Celem.

Record handshake :=
  { req : name
  ; ack : name }.

Import MonadNotations.
Variable Fresh : Type -> Type.
Context `{FreshM : Monad Fresh}.
Variable fresh_ : Fresh name.
Variable fail_ : Fresh name.


Section Split.

  Definition forward x y := comb _ (singleton x) y (fun σ => σ x).
  Definition output x (v : option value) := 
    comb _ ∅ x (fun σ => match v with
                         | None => σ x
                         | Some v' => v'
                         end).


  Fixpoint nary_C (i : name) (I : list name) (o : name) : Fresh (CircuitStateSpace name) :=
    match I with
    | nil => return_ (forward i o)
    | i' :: I' => do x ← fresh_;
                  let C_i_i' := ss_C i i' x in
                  do C_x_I' ← nary_C x I' o;
                  return_ (C_i_i' ∥ C_x_I')
    end.


Print CircuitStateSpace.

  Definition ss_empty : CircuitStateSpace name :=
  {| css_input := ∅
   ; css_output := ∅
   ; css_internal := ∅
   ; css_step := fun _ _ _ => False |}.
  Fixpoint nary_union (Ss : list (CircuitStateSpace name)) : CircuitStateSpace name :=
    match Ss with
    | nil => ss_empty
    | S0 :: Ss' => S0 ∥ nary_union Ss'
    end.
    


  Definition wire_fork x y1 y2 := forward x y1 ∥ forward x y2.
  Definition nary_wire_fork i (O : list name) := nary_union (fmap (forward i) O).

  Definition split (i o1 o2 : handshake) :=
    wire_fork (req i) (req o1) (req o2)
    ∥ ss_C (ack o1) (ack o2) (ack i).

  Definition split_n (i : handshake) (os : list handshake) : Fresh (CircuitStateSpace name) :=
    match os with
    | nil => return_ (forward (req i) (ack i))
    | o :: os' => let F := nary_wire_fork (req i) (req o :: fmap req os) in
                  do C ← nary_C (ack o) (fmap ack os') (ack i);
                  return_ (F ∥ C)
    end.

  Definition join (i1 i2 o : handshake) :=
    wire_fork (ack o) (ack i1) (ack i2)
    ∥ ss_C (req i1) (req i2) (req o).
  Definition join_n (is : list handshake) (o : handshake) : Fresh (CircuitStateSpace name) :=
    match is with
    | nil => return_ (forward (ack o) (req o))
    | i :: is' => let F := nary_wire_fork (ack o) (ack i :: fmap ack is') in
                  do C ← nary_C (req i) (fmap req is') (req i);
                  return_ (F ∥ C)
    end.

End Split.

  Require Import List.
  Import ListNotations.
  Open Scope list_scope.


  Fixpoint from_list (l : list name) : Ensemble name :=
    match l with
    | nil => ∅
    | x :: l' => singleton x ∪ from_list l'
    end.




Lemma not_in_singleton_neq : forall (x y : name),
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
    find_contradiction.
Qed.
Hint Resolve not_in_singleton_neq : sets.

  (** Sanity checks *)

Lemma Setminus_in : forall x (X Y : Ensemble name),
    x ∈ X ∖ Y ->
    (x ∈ X).
Admitted.
Lemma Setminus_not_in : forall x (X Y : Ensemble name),
    x ∈ X ∖ Y ->
    ~(x ∈ Y).
Admitted.
Hint Resolve Setminus_in Setminus_not_in : sets.

Lemma not_union_1 : forall (x : name) X Y,
    ~(x ∈ X ∪ Y) ->
    ~(x ∈ X).
Admitted.
Lemma not_union_2 : forall (x : name) X Y,
    ~(x ∈ X ∪ Y) ->
    ~(x ∈ X).
Admitted.
Hint Resolve not_union_1 not_union_2 : sets.


Inductive all_disjoint : list name -> Prop :=
| nil_disjoint : all_disjoint []
| cons_disjoint x ls : 
    x ∉ from_list ls ->
    all_disjoint ls ->
    all_disjoint (x::ls).

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


Section Stage.

  Variable i o : handshake.
  Variable ctrl_reset_n dp_reset_n : name.
  Variable clk old_clk state0 : name.

  Hypothesis domain_disjoint : all_disjoint [req i; ack i; req o; ack o;
                                             ctrl_reset_n; dp_reset_n;
                                             clk; old_clk; state0].

(*
  Definition clk_defn :=    ((not (req i)) /\ state0 /\ ack o)
                         \/ (req i /\ not (state0) /\ not (ack o)).
*)
  Definition clk_defn σ :=
    match σ (req i) , σ state0 , σ (ack o) with
    | Num 0, Num 1, Num 1 => Num 1
    | Num 1, Num 0, Num 0 => Num 1
    | Num _, Num _, Num _ => Num 0
    | _    , _    , _     => X
    end.
  Definition tok_clk_defn σ :=
    match σ (req i) , σ state0 , σ (ack o) with
    | Num 1, Num 1, Num 1 => Num 1
    | Num 0, Num 0, Num 0 => Num 1
    | Num _, Num _, Num _ => Num 0
    | _    , _    , _     => X
    end.

  Definition clk_component := comb _ (from_list [state0;req i;ack o;ctrl_reset_n]) clk clk_defn.
  Definition tok_clk_component := comb _ (from_list [state0;req i;ack o;ctrl_reset_n]) clk tok_clk_defn.

  Definition negate i o := comb _ (singleton i) o (fun σ => neg_value (σ i)).
  
  Definition stage :=
    clk_component ∥ flop dp_reset_n clk old_clk state0 (Num 0) 
                  ∥ forward state0 (ack i) ∥ forward state0 (req o).
  Definition token_stage :=
    clk_component ∥ flop dp_reset_n clk old_clk state0 (Num 1)
                  ∥ negate state0 (ack i) ∥ forward state0 (req o).

  Lemma stage_input : css_input stage == from_list [req i;ack o;dp_reset_n;ctrl_reset_n].
  Proof.
    constructor; intros x Hx; simpl in *; decompose_set_structure; solve_set.
  Qed.

  Lemma stage_output : css_output stage == from_list [ack i;req o;state0;clk].
  Proof.
    constructor; intros x Hx; simpl in *; decompose_set_structure.
  Qed.

  Lemma stage_internal : css_internal stage == singleton old_clk.
  Proof.
    constructor; intros x Hx; simpl in *; decompose_set_structure.
  Qed.
  Lemma token_stage_input : css_input token_stage == from_list [req i;ack o;dp_reset_n;ctrl_reset_n].
  Proof.
    constructor; intros x Hx; simpl in *; decompose_set_structure; solve_set.
  Qed.

  Lemma token_stage_output : css_output token_stage == from_list [ack i;req o;state0;clk].
  Proof.
    constructor; intros x Hx; simpl in *; decompose_set_structure.
  Qed.

  Lemma token_stage_internal : css_internal token_stage == singleton old_clk.
  Proof.
    constructor; intros x Hx; simpl in *; decompose_set_structure.
  Qed.


End Stage.


Section Desync.

  Variable even odd : Set.
  Variable c : circuit even odd.

  (* each latch has an associated input and output handshake *)
  Variable latch_input : latch even odd -> handshake.
  Variable latch_output : latch even odd -> handshake.
  Variable latch_clk : latch even odd -> name.
  Variable latch_state0 : latch even odd -> name.
  Variable latch_old_clk : latch even odd -> name.
  Variable ctrl_reset_n dp_reset_n : name.

  Definition latch_stage (l : latch even odd) : CircuitStateSpace name :=
    match l with
    | Even _ => token_stage (latch_input l) (latch_output l)
                            ctrl_reset_n dp_reset_n
                            (latch_clk l) (latch_old_clk l) (latch_state0 l)
    | Odd _ => stage (latch_input l) (latch_output l)
                     ctrl_reset_n dp_reset_n
                     (latch_clk l) (latch_old_clk l) (latch_state0 l)
    end.
Print circuit.
Print neighbor.
Print split_n.

Search ((list (list ?A)) -> list ?A).
About concat.
About "++".
Search (list (option ?A) -> list ?A).
  Context `{eq_dec even} `{eq_dec odd}.
Search latch eq_dec.
    Existing Instance latch_eq_dec.
  Definition right_neighbors_of (l : latch even odd) (c : circuit even odd) : list (latch even odd) :=
    let f_eo := fun (eo_neighbor : even * odd) =>
                    let (E,O) := eo_neighbor in
                    if l =? (Even E) then (Odd O :: [])
                    else nil : list (latch even odd)
    in
    let f_oe := fun (oe_neighbor : odd * even) =>
                    let (O,E) := oe_neighbor in
                    if l =? (Odd O) then (Even E :: nil)
                    else nil : list (latch even odd)
    in
    let even_right_neighbors := concat (fmap f_eo (even_odd_neighbors c))in
    let odd_right_neighbors := concat (fmap f_oe (odd_even_neighbors c)) in
    even_right_neighbors ++ odd_right_neighbors.


  Definition left_neighbors_of (l : latch even odd) (c : circuit even odd) : list (latch even odd) :=
    let f_eo := fun (eo_neighbor : even * odd) =>
                    let (E,O) := eo_neighbor in
                    if l =? (Odd O) then (Even E :: [])
                    else nil : list (latch even odd)
    in
    let f_oe := fun (oe_neighbor : odd * even) =>
                    let (O,E) := oe_neighbor in
                    if l =? Even E then (Odd O :: nil)
                    else nil : list (latch even odd)
    in
    let even_left_neighbors := concat (fmap f_eo (even_odd_neighbors c))in
    let odd_left_neighbors := concat (fmap f_oe (odd_even_neighbors c)) in
    even_left_neighbors ++ odd_left_neighbors.


Print join_n.
  Definition neighbor_split (l : latch even odd) :=
    let ls := right_neighbors_of l c in
    split_n (latch_output l) (fmap latch_input (right_neighbors_of l c)).
  Definition neighbor_join (l : latch even odd) :=
    let ls := left_neighbors_of l c in
    join_n (fmap latch_output (left_neighbors_of l c)) (latch_input l).

  Class enumerable (A : Set) :=
  { enumerate : list A
  ; enumerate_proof : forall (a : A), In a enumerate
  }.

  Arguments enumerate A : clear implicits.

  Context `{enum_even : enumerable even} `{enum_odd : enumerable odd}.

Lemma in_fmap : forall X Y (x : X) (ls : list X) (f : X -> Y),
    In x ls ->
    In (f x) (fmap f ls).
Proof.
  intros X Y x ls;
    induction ls as [ | y ls']; intros f Hin.
  * inversion Hin.
  * inversion Hin; subst.
    + simpl. auto.
    + simpl.
      right.
      apply IHls'; auto.
Qed.
  Instance latch_enumerable : enumerable (latch even odd).
  Proof.
    exists (fmap Even (enumerate even _) ++ fmap Odd (enumerate odd _) : list (latch even odd)).
    intros [O | E]; apply in_or_app.
    * right. 
      apply in_fmap.
      apply enumerate_proof.
    * left.
      apply in_fmap.
      apply enumerate_proof.
  Defined.

About neighbor_split.

Fixpoint sequence {N} `{Monad N} {A} (l : list (N A)) : N (list A) :=
  match l with
  | nil => return_ nil
  | n :: l' => do a ← n;
               do l'' ← sequence l';
               return_ (a :: l'')
  end.

  Definition desynchronize : Fresh (CircuitStateSpace name) :=
    let latches := enumerate (latch even odd) _ in
    let stages := fmap latch_stage latches in
    do neighbor_splits ← sequence (fmap neighbor_split latches);
    do neighbor_joins ← sequence (fmap neighbor_join latches);
    return_ (nary_union stages ∥ nary_union neighbor_splits ∥ nary_union neighbor_joins).


End Desync.

End Click.
