Require Import Base.
Require Import FlowEquivalence.
Require Import StateSpace.
Require Import Monad.

Require Import List.
Import ListNotations.
Open Scope list_scope.


Section Click.

Variable name : Set.
Context `{eq_dec name}.
Import EnsembleNotation.
Open Scope ensemble_scope.


Record handshake :=
  { req : name
  ; ack : name }.

Import MonadNotations.
Variable Fresh : Type -> Type.
Context `{FreshM : Monad Fresh}.
Variable fresh_ : Fresh name.
Variable fail_ : Fresh name.


Section Split.

  Definition forward x y := func_space (singleton x) y (fun σ => σ x).
  Definition output x (v : option value) := 
    func_space ∅ x (fun σ => match v with
                         | None => σ x
                         | Some v' => v'
                         end).


  Fixpoint nary_C (i : name) (I : list name) (o : name) : Fresh (StateSpace name) :=
    match I with
    | nil => return_ (forward i o)
    | i' :: I' => do x ← fresh_;
                  let C_i_i' := C_elem i i' x in
                  do C_x_I' ← nary_C x I' o;
                  return_ (C_i_i' ∥ C_x_I')
    end.


  Definition ss_empty : StateSpace name :=
  {| space_input := ∅
   ; space_output := ∅
   ; space_internal := ∅
   ; space_step := fun _ _ _ => False |}.
  Fixpoint nary_union (Ss : list (StateSpace name)) : StateSpace name :=
    match Ss with
    | nil => ss_empty
    | S0 :: Ss' => S0 ∥ nary_union Ss'
    end.
    


  Definition wire_fork x y1 y2 := forward x y1 ∥ forward x y2.
  Definition nary_wire_fork i (O : list name) := nary_union (fmap (forward i) O).

  Definition split (i o1 o2 : handshake) :=
    wire_fork (req i) (req o1) (req o2)
    ∥ C_elem (ack o1) (ack o2) (ack i).

  Definition split_n (i : handshake) (os : list handshake) : Fresh (StateSpace name) :=
    match os with
    | nil => return_ (forward (req i) (ack i))
    | o :: os' => let F := nary_wire_fork (req i) (req o :: fmap req os) in
                  do C ← nary_C (ack o) (fmap ack os') (ack i);
                  return_ (F ∥ C)
    end.

  Definition join (i1 i2 o : handshake) :=
    wire_fork (ack o) (ack i1) (ack i2)
    ∥ C_elem (req i1) (req i2) (req o).
  Definition join_n (is : list handshake) (o : handshake) : Fresh (StateSpace name) :=
    match is with
    | nil => return_ (forward (ack o) (req o))
    | i :: is' => let F := nary_wire_fork (ack o) (ack i :: fmap ack is') in
                  do C ← nary_C (req i) (fmap req is') (req i);
                  return_ (F ∥ C)
    end.

End Split.

  (** Sanity checks *)



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

  Definition clk_component := func_space (from_list [state0;req i;ack o;ctrl_reset_n]) clk clk_defn.
  Definition tok_clk_component := func_space (from_list [state0;req i;ack o;ctrl_reset_n]) clk tok_clk_defn.

  Definition negate i o := func_space (singleton i) o (fun σ => neg_value (σ i)).
  
  Definition stage :=
    clk_component ∥ flop dp_reset_n clk old_clk state0 (Num 0) 
                  ∥ forward state0 (ack i) ∥ forward state0 (req o).
  Definition token_stage :=
    clk_component ∥ flop dp_reset_n clk old_clk state0 (Num 1)
                  ∥ negate state0 (ack i) ∥ forward state0 (req o).

  Lemma stage_input : space_input stage == from_list [req i;ack o;dp_reset_n;ctrl_reset_n].
  Proof.
    constructor; intros x Hx; simpl in *; decompose_set_structure; solve_set.
  Qed.

  Lemma stage_output : space_output stage == from_list [ack i;req o;state0;clk].
  Proof.
    constructor; intros x Hx; simpl in *; decompose_set_structure.
  Qed.

  Lemma stage_internal : space_internal stage == singleton old_clk.
  Proof.
    constructor; intros x Hx; simpl in *; decompose_set_structure.
  Qed.
  Lemma token_stage_input : space_input token_stage == from_list [req i;ack o;dp_reset_n;ctrl_reset_n].
  Proof.
    constructor; intros x Hx; simpl in *; decompose_set_structure; solve_set.
  Qed.

  Lemma token_stage_output : space_output token_stage == from_list [ack i;req o;state0;clk].
  Proof.
    constructor; intros x Hx; simpl in *; decompose_set_structure.
  Qed.

  Lemma token_stage_internal : space_internal token_stage == singleton old_clk.
  Proof.
    constructor; intros x Hx; simpl in *; decompose_set_structure.
  Qed.


End Stage.


Section Desync.

  Variable even odd : Set.
  Context `{eq_dec_even : eq_dec even} `{eq_dec_odd : eq_dec odd}.
  Existing Instance latch_eq_dec.

  Variable c : circuit even odd.

  (* each latch has an associated input and output handshake *)
  Variable latch_input : latch even odd -> handshake.
  Variable latch_output : latch even odd -> handshake.
  Variable latch_clk : latch even odd -> name.
  Variable latch_state0 : latch even odd -> name.
  Variable latch_old_clk : latch even odd -> name.
  Variable ctrl_reset_n dp_reset_n : name.

  Definition latch_stage (l : latch even odd) : StateSpace name :=
    match l with
    | Even _ => token_stage (latch_input l) (latch_output l)
                            ctrl_reset_n dp_reset_n
                            (latch_clk l) (latch_old_clk l) (latch_state0 l)
    | Odd _ => stage (latch_input l) (latch_output l)
                     ctrl_reset_n dp_reset_n
                     (latch_clk l) (latch_old_clk l) (latch_state0 l)
    end.

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

Fixpoint sequence {N} `{Monad N} {A} (l : list (N A)) : N (list A) :=
  match l with
  | nil => return_ nil
  | n :: l' => do a ← n;
               do l'' ← sequence l';
               return_ (a :: l'')
  end.

  Definition desynchronize : Fresh (StateSpace name) :=
    let latches := enumerate (latch even odd) _ in
    let stages := fmap latch_stage latches in
    do neighbor_splits ← sequence (fmap neighbor_split latches);
    do neighbor_joins ← sequence (fmap neighbor_join latches);
    return_ (nary_union stages ∥ nary_union neighbor_splits ∥ nary_union neighbor_joins).


End Desync.

End Click.