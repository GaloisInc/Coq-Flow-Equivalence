Require Import Base.
Require Import Circuit.
Require Import StateSpace.
Require Import Monad.

Require Import List.
Import ListNotations.
Open Scope list_scope.

Require Import Omega.

Section Click. 

Set Implicit Arguments.

(** * Define click circuits at state spaces, building off of StateSpace.v *)

Variable name : Set.
Context `{eq_dec name}.
Import EnsembleNotation.
Open Scope ensemble_scope.

(** A handshake has two names: [req h] and [ack h]. *)
Record handshake :=
  { req : name
  ; ack : name }.


(** Here, I am trying to introduce a monad that can produce a fresh variable. It
might be a better idea to just fix [name] to be e.g. [string] and manually
ensure that we get fresh names, because the monad is really hard to work with,
espeically at the top level. *)
Import MonadNotations.
Variable Fresh : Type -> Type.
Context `{FreshM : Monad Fresh}.
Variable fresh_ : Fresh name.
Variable fail_ : Fresh name.

Variable run_fresh : forall {A}, Fresh A -> A.

Section Utils.
  (** [forward x y] is the state space that updates [y] (the output) to have the
  same value as [x] (the input). *)
  Definition forward x y := func_space (singleton x) y (fun σ => σ x).
  (** [output x (Some v)] is the state space that updates [x] (the output) to
  have the value [v].

    [output x None] is the state space that simply treats [x] as an output whose
value never changes. When composed with a state space where [x] is an input,
this turns [x] from an input to an output in the union space. *)
  Definition output x (v : option value) :=
    func_space ∅ x (fun σ => match v with
                         | None => σ x
                         | Some v' => v'
                         end).

  (** An inverter *)
  Definition NOT x y := func_space (singleton x) y (fun σ => neg_value (σ x)).


  (** The empty state space with no wires and no transitions *)
  Definition space_empty : StateSpace name :=
  {| space_input := ∅
   ; space_output := ∅
   ; space_internal := ∅
   ; space_step := fun _ _ _ => False |}.

  (** Take the n-ary union of all the state spaces in the list [Ss] *)
  Fixpoint nary_union (Ss : list (StateSpace name)) : StateSpace name :=
    match Ss with
    | nil => space_empty
    | S0 :: Ss' => S0 ∥ nary_union Ss'
    end.

End Utils.


(** * Define a state space modeling a binary and n-ary split from one handshake
to a pair or list of handshakes. This is made by composing a C element (for the
acknowledgement wires) with an wire fork (for the request wires).

Vice versa for binary and n-ary joins *)
Section Split.

  Definition wire_fork x y1 y2 := forward x y1 ∥ forward x y2.
  (** Binary split *)
  Definition split (i o1 o2 : handshake) :=
    wire_fork (req i) (req o1) (req o2)
    ∥ C_elem (ack o1) (ack o2) (ack i).
  (** Binary join *)
  Definition join (i1 i2 o : handshake) :=
    wire_fork (ack o) (ack i1) (ack i2)
    ∥ C_elem (req i1) (req i2) (req o).


  (** The n-ary C element is annoying because it requires we come up with fresh
  wire names for the internal wires. Perhaps a better choice would be: internal
  wires are always disjoint, so encode them as a type e.g. internal (S1 ∥ S2) =
  internal S1 + internal S2. Or else, keep them as names (strings) and internal
  (S1 ∥ S2) = "S1."++internal(S1) ∪ "S2."++internal(S2). This ensures we only
  have to worry about local uniqueness of the names.
  *)
  Fixpoint nary_C (i : name) (I : list name) (o : name) : Fresh (StateSpace name) :=
    match I with
    | nil => return_ (forward i o)
    | i' :: I' => do x ← fresh_;
                  let C_i_i' := C_elem i i' x in
                  do C_x_I' ← nary_C x I' o;
                  return_ (C_i_i' ∥ C_x_I')
    end.
  Definition nary_wire_fork i (O : list name) := nary_union (fmap (forward i) O).

  (** n-ary split *)
  Definition split_n (i : handshake) (os : list handshake) : Fresh (StateSpace name) :=
    match os with
    | nil => return_ (forward (req i) (ack i))
    | o :: os' => let F := nary_wire_fork (req i) (req o :: fmap req os) in
                  do C ← nary_C (ack o) (fmap ack os') (ack i);
                  return_ (F ∥ C)
    end.

  (** n-ary join *)
  Definition join_n (is : list handshake) (o : handshake) : Fresh (StateSpace name) :=
    match is with
    | nil => return_ (forward (ack o) (req o))
    | i :: is' => let F := nary_wire_fork (ack o) (ack i :: fmap ack is') in
                  do C ← nary_C (req i) (fmap req is') (req i);
                  return_ (F ∥ C)
    end.

End Split.

(** * Define an ordinary Click stage, both token and non-token variants. *)
Section Stage.

  (** 1. declare all wire names *)

  Variable i o : handshake.
  Variable ctrl_reset_n dp_reset_n hidden_reset : name.
  Variable clk old_clk state0 not_state0 : name.

  Hypothesis domain_disjoint : all_disjoint [req i; ack i; req o; ack o;
                                             ctrl_reset_n; dp_reset_n;
                                             hidden_reset;
                                             clk; old_clk; state0; not_state0].

  (** 2. Define the combinational logic that drives the clock *)
(*
  Definition clk_defn :=    ((not (req i)) /\ state0 /\ ack o)
                         \/ (req i /\ not (state0) /\ not (ack o)).
*)
  Definition clk_defn σ :=
    match σ ctrl_reset_n, σ (req i) , σ state0 , σ (ack o) with
    | Num 0, _    , _    , _     => Num 0
    | Num 1, Num 0, Num 1, Num 1 => Num 1
    | Num 1, Num 1, Num 0, Num 0 => Num 1
    | Num 1, Num _, Num _, Num _ => Num 0
    | _    ,_    , _    , _     => X
    end.
  Definition tok_clk_defn σ :=
    match σ ctrl_reset_n, σ (req i) , σ state0 , σ (ack o) with
    | Num 0, _    , _    , _     => Num 0
    | Num 1, Num 1, Num 1, Num 1 => Num 1
    | Num 1, Num 0, Num 0, Num 0 => Num 1
    | Num 1, Num _, Num _, Num _ => Num 0
    | _    , _    , _    , _     => X
    end.

  Inductive token_flag := Token | NonToken.

  Definition clk_component f := 
    func_space (from_list [state0;req i;ack o;ctrl_reset_n]) clk (match f with
                                                                  | NonToken => clk_defn
                                                                  | Token    => tok_clk_defn
                                                                  end).

(*
  Let flop_component' (f : token_flag) :=
    match f with
    | Token    => flop dp_reset_n   hidden_reset clk old_clk not_state0 state0
    | NonToken => flop hidden_reset dp_reset_n   clk old_clk not_state0 state0
    end.
*)
  (** 3. Define the flip flop components *)
  Definition flop_component f := 
    let flop_set := match f with
                     | Token => dp_reset_n
                     | NonToken => hidden_reset
                     end in
    let flop_reset := match f with
                     | Token => hidden_reset
                     | NonToken => dp_reset_n
                     end in
      hide not_state0
    ( hide hidden_reset
    ( flop flop_set flop_reset clk old_clk not_state0 state0
    ∥ NOT state0 not_state0
    ∥ output hidden_reset (Some (Num 1)))).

  (** 4. Combine these components. We define variants with reset, as well as
  variants where the reset inputs remain stable, meaning that reset is not a
  factor. *)
  Definition latch_to_token_flag {even odd} (l : latch even odd) :=
    match l with
    | Odd _ => NonToken
    | Even _ => Token
    end.

  Definition ack_i_output f := match f with
                            | Token => NOT state0 (ack i)
                            | NonToken => forward state0 (ack i)
                            end.

  Definition stage_with_reset (f : token_flag) :=
    clk_component f ∥ flop_component f ∥ forward state0 (req o) ∥ ack_i_output f.

  Definition stage (f : token_flag) :=
      hide state0 
    ( hide dp_reset_n
    ( hide ctrl_reset_n
    ( stage_with_reset f ∥ output dp_reset_n None ∥ output ctrl_reset_n None))).


  (** Some lemmas to act as sanity checks that the definitions are correct, and to test automation *)
  Lemma stage_with_reset_input : forall f,
    space_input (stage_with_reset f) == from_list [req i;ack o;dp_reset_n;ctrl_reset_n].
  Proof.
    intros [ | ];
    constructor; intros x Hx; simpl in *; decompose_set_structure; solve_set.
  Qed.

  Lemma stage_with_reset_output : forall f,
    space_output (stage_with_reset f) == from_list [ack i;req o;state0;clk].
  Proof.
    intros [ | ];
    constructor; intros x Hx; simpl in *; decompose_set_structure; solve_set.
  Qed.

  Lemma stage_with_reset_internal_NT : forall f,
    space_internal (stage_with_reset f) == from_list [old_clk; hidden_reset; not_state0].
  Proof.
    intros [ | ];
    constructor; intros x Hx; simpl in *; decompose_set_structure; solve_set.
  Qed.

 Lemma stage_input : forall f,
    space_input (stage f) == from_list [req i;ack o].
  Proof.
    intros [ | ];
    constructor; intros x Hx; simpl in *; decompose_set_structure; solve_set.
  Qed.

  Lemma stage_output : forall f,
    space_output (stage f) == from_list [ack i;req o;clk].
  Proof.
    intros [ | ];
    constructor; intros x Hx; simpl in *; decompose_set_structure; solve_set.
  Qed.

End Stage.

(** * Desynchronize a circuit (see Circuit.v) and produce the set of intertwined
Click controllers that will drive the local clocks. *)


Section Desync.

  Variable even odd : Set.
  Context `{eq_dec_even : eq_dec even} `{eq_dec_odd : eq_dec odd}.
  Existing Instance latch_eq_dec.

  Class naming_scheme :=
    { latch_input : latch even odd -> handshake
    ; latch_output : latch even odd -> handshake
    ; latch_clk : latch even odd -> name
    ; latch_state0 : latch even odd -> name
    ; latch_old_clk : latch even odd -> name
    ; latch_not_state0 : latch even odd -> name
    ; latch_hidden : latch even odd -> name
    ; ctrl_reset_n : name
    ; dp_reset_n : name

    ; scheme_all_disjoint : forall l, all_disjoint
       [req (latch_input l); ack (latch_input l);
        req (latch_output l); ack (latch_output l);
        ctrl_reset_n; dp_reset_n; latch_hidden l;
        latch_clk l; latch_old_clk l;
        latch_state0 l; latch_not_state0 l]

    }.
  Context `{scheme : naming_scheme}.

  Variable c : circuit even odd.

  Definition is_token_latch (l : latch even odd) :=
    match l with
    | Even _ => true
    | Odd  _ => false
    end.

  (** The state obtained by the reset procedure relevant to this particular
  stage... really, this should be defined concurrently for all stages. *)
  Definition σR (l : latch even odd) : state name :=
    fun x =>
      (* acknowledgments are 0 *)
      if x =? ack (latch_output l) then Bit0
      else if x =? ack (latch_input l) then Bit0

      (* if l is a token latch, then its left neighbor is a non-token latch, so
         its left request wire will be 0; vice versa for non-token latch *)
      else if x =? req (latch_input l) then (if is_token_latch l then Bit0 else Bit1)
      (* if l is a token latch, then it will output a 1 on its right request;
      vice versa for a non-token latch *)
      else if x =? req (latch_output l) then (if is_token_latch l then Bit1 else Bit0)
      else if x =? latch_state0 l then Bit1
      else if x =? latch_not_state0 l then Bit0
      (* clock starts out 0 *)
      else if x =? latch_clk l then Bit0
      else if x =? latch_old_clk l then Bit0
      (* reset wires start at 1 *)
      else if x =? dp_reset_n then Bit1
      else if x =? ctrl_reset_n then Bit1
      else if x =? latch_hidden l then Bit1
      else Bit0.

  (** even latches are driven by token controllers, while odd latches are driven by non-token controllers. 

    TODO: is this opposite?
    *)
    (*
  Definition latch_stage (l : latch even odd) : StateSpace name :=
    stage (latch_input l) (latch_output l)
          ctrl_reset_n dp_reset_n
          (latch_hidden l)
          (latch_clk l) (latch_old_clk l) (latch_state0 l) (latch_not_state0 l)
          (latch_to_token_flag l).
*)

  Definition latch_flop_component (l : latch even odd) : StateSpace name :=
    flop_component dp_reset_n (latch_hidden l)
                   (latch_clk l) (latch_old_clk l)
                   (latch_state0 l) (latch_not_state0 l)
                   (latch_to_token_flag l).
  Definition latch_clk_component (l : latch even odd) : StateSpace name :=
    clk_component (latch_input l) (latch_output l) ctrl_reset_n (latch_clk l) (latch_state0 l)
                  (latch_to_token_flag l).
  Definition latch_right_req_component (l : latch even odd) :=
    forward (latch_state0 l) (req (latch_output l)).
  Definition latch_left_ack_component (l : latch even odd) :=
    ack_i_output (latch_input l) (latch_state0 l) (latch_to_token_flag l).
  Definition latch_stage_with_reset l :=
      latch_clk_component l ∥ latch_flop_component l
    ∥ latch_left_ack_component l ∥ latch_right_req_component l.
  Definition latch_stage (l : latch even odd) :=
      hide (latch_state0 l)
    ( hide dp_reset_n
    ( hide ctrl_reset_n
    ( latch_stage_with_reset l ∥ output dp_reset_n None ∥ output ctrl_reset_n None ))).



 Lemma latch_stage_input : forall l,
    space_input (latch_stage l) == from_list [req (latch_input l);ack (latch_output l)].
  Proof.
    intro l.
    set (Hdisjoint := scheme_all_disjoint l).
    destruct l;
    constructor; intros x Hx; simpl in *; decompose_set_structure; solve_set.
  Qed.

  Lemma latch_stage_output : forall l,
    space_output (latch_stage l) == from_list [ack (latch_input l);req (latch_output l);latch_clk l].
  Proof.
    intro l.
    set (Hdisjoint := scheme_all_disjoint l).
    destruct l;
    constructor; intros x Hx; simpl in *; decompose_set_structure; solve_set.
  Qed.


  (** In order to add the appropriate splits and joins, we need a *function*
  that produces a list of all the right (resp. left) neighbors of a latch [l].
  This is pretty ugly currently, but could be improved. *)
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


  (** Produce the appropriate split and join components for a particular latch. *)
  Definition neighbor_split (l : latch even odd) :=
    let ls := right_neighbors_of l c in
    split_n (latch_output l) (fmap latch_input (right_neighbors_of l c)).
  Definition neighbor_join (l : latch even odd) :=
    let ls := left_neighbors_of l c in
    join_n (fmap latch_output (left_neighbors_of l c)) (latch_input l).

  (** TODO: move this to a more appropriate location. *)
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

  (** Produce the desynchronized asynchronous controller *)
  Definition desynchronize : Fresh (StateSpace name) :=
    let latches := enumerate (latch even odd) _ in
    let stages := fmap latch_stage latches in
    do neighbor_splits ← sequence (fmap neighbor_split latches);
    do neighbor_joins ← sequence (fmap neighbor_join latches);
    return_ (nary_union stages ∥ nary_union neighbor_splits ∥ nary_union neighbor_joins).


End Desync.

End Click.

Arguments latch_input  {name even odd} {naming_scheme}.
Arguments latch_output {name even odd} {naming_scheme}.
Arguments latch_clk    {name even odd} {naming_scheme}.
Arguments latch_state0 {name even odd} {naming_scheme}.
Arguments latch_old_clk {name even odd} {naming_scheme}.
Arguments latch_not_state0 {name even odd} {naming_scheme}.
Arguments latch_hidden {name even odd} {naming_scheme}.
Arguments ctrl_reset_n {name even odd} {naming_scheme}.
Arguments dp_reset_n {name even odd} {naming_scheme}.

Arguments req {name}.
Arguments ack {name}.

Arguments latch_stage {name} {name_dec} {even odd} {naming_scheme} : rename.
Arguments σR {name} {name_dec} {even odd} {naming_scheme} l : rename.
