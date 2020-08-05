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

  Definition ack_i_output f := (*match f with
                            | Token => NOT state0 (ack i)
                            | NonToken => forward state0 (ack i)
                            end.*)
    func_space (singleton state0) (ack i) (fun σ => match f with
                                                    | Token => neg_value (σ state0)
                                                    | NonToken => σ state0
                                                    end).

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

Arguments well_formed {name}.

Section WF_stage.

  Variable even odd : Set.
  Context {scheme : naming_scheme even odd}.

  Definition left_env_component (l : latch even odd) :=
    NOT (ack (latch_input l)) (req (latch_input l)).
  Definition right_env_component (l : latch even odd) :=
    forward (req (latch_output l)) (ack (latch_output l)).


(*  any click circuit with output ho, input handshake hi:
    C ⊆ left_env_component ho ∥ right_env_component hi

   l -> l'
   l -> l''

   latch_stage l = state space with clock l
   stageMG l = marked graph (as a state space)

    hide l''_in ((stageMG l ∥ fanout l_out l'_in l''_in) ∥ stageMG l')
    ⊆ stageMG l [l_out ↦ l'_in] ∥ stageMG l'

    if t ∈ hide everything else except local clocks (C ∥ latch_stage l ∥ latch_stage l')

    fanout h h1 h2 ⊆ h ↔ h1 ∥ h ↔ h2
    then t ∈ (left_env_component ∥ latch_stage l ∥ lout ↔ lin ∥ latch_stage l' ∥ right_env_component)
    modulo hiding

    and we are proving therefore t ∈ rise_decoupled
*)
  Definition latch_stage_with_env l := left_env_component l ∥ latch_stage l ∥ right_env_component l.


  Lemma latch_stage_with_env_input : forall l,
    space_input (latch_stage_with_env l) == ∅.
  Proof.
    intros l'. split.
    2:{ intros x Hx; inversion Hx. }
    set (Hdisjoint := scheme_all_disjoint l').
    intros x Hx. simpl in Hx. decompose_set_structure.
    destruct l'; simpl in *; decompose_set_structure; find_contradiction.
    destruct l'; simpl in *; decompose_set_structure; find_contradiction.
  Qed.
  Lemma latch_stage_with_env_output : forall l,
    space_output (latch_stage_with_env l) == space_input (latch_stage l) ∪ space_output (latch_stage l).
  Proof.
    intros l'.
    set (Hdisjoint := scheme_all_disjoint l').
    split.
    { intros x Hx. simpl in Hx. decompose_set_structure;
      destruct l'; simpl in *; decompose_set_structure; solve_set.
    }
    { intros x Hx. simpl in Hx. decompose_set_structure;
      destruct l'; simpl in *; decompose_set_structure; solve_set.
    }
  Qed.
  Lemma latch_stage_with_env_internal : forall l,
    space_internal (latch_stage_with_env l) == space_internal (latch_stage l).
  Proof.
    intros l'.
    set (Hdisjoint := scheme_all_disjoint l').
    split.
    { intros x Hx. simpl in Hx. decompose_set_structure;
      destruct l'; simpl in *; decompose_set_structure; solve_set.
    }
    { intros x Hx. simpl in Hx. decompose_set_structure;
      destruct l'; simpl in *; decompose_set_structure; solve_set.
    }
  Qed.
  Lemma dom_latch_stage_with_env : forall l,
    space_domain (latch_stage_with_env l) == space_domain (latch_stage l).
  Proof.
    intros l'.
    unfold space_domain.
    rewrite latch_stage_with_env_input.
    rewrite latch_stage_with_env_output.
    rewrite latch_stage_with_env_internal.
    (* monoid *)
    admit.
  Admitted.


  Inductive val_is_bit : value -> Prop :=
  | val_bit0 : val_is_bit Bit0
  | val_bit1 : val_is_bit Bit1.
  Lemma val_is_bit_neg_neg : forall v, val_is_bit v -> neg_value (neg_value v) = v.
  Proof.
    intros v Hv; inversion Hv; subst; auto.
  Qed.
  Lemma val_is_bit_neq : forall v1 v2, val_is_bit v1 -> val_is_bit v2 -> v1 <> v2 -> neg_value v1 = v2.
  Proof.
    intros v1 v2 Hv1 Hv2 Hneq;
      inversion Hv1; inversion Hv2; subst; auto;
        find_contradiction.
  Qed.
  Lemma val_is_bit_neg_inversion : forall v1 v2, val_is_bit v2 ->
                                                 v1 = neg_value v2 ->
                                                 neg_value v1 = v2.
  Proof.
    intros v1 v2 Hv2 Heq; subst. rewrite val_is_bit_neg_neg; auto.
  Qed.

  Hint Constructors val_is_bit : click.
  Inductive wf_handshake (h : handshake) (σ : state name) : Prop :=
  | handshake_in_sync : σ (req h) = σ (ack h) -> wf_handshake h σ
  | handshake_out_of_sync : σ (req h) = neg_value (σ (ack h)) -> wf_handshake h σ.
  Record wf_stage_state (l : latch even odd) (σ : state name) : Prop :=
    { wf_all_bits : forall x, x ∈ space_domain (latch_stage_with_env l) -> val_is_bit (σ x)
    ; wf_latch_input  : wf_handshake (latch_input l)  σ
    ; wf_latch_output : wf_handshake (latch_output l) σ
    ; wf_ctrl_reset_n : σ (@ctrl_reset_n even odd _) = Bit1
    }.

  Lemma step_wf_state_σR : forall l,
    wf_stage_state l (σR l).
  Proof.
    intros l.
    set (Hdisjoint := scheme_all_disjoint l).
      split.
      { intros x Hx. unfold σR.
        repeat (compare_next; try constructor);
          destruct l; try constructor.
      }
      { assert (Hack : σR l (ack (latch_input l)) = Bit0).
        { unfold σR; reduce_eqb.
          repeat (compare_next; auto).
        }
        assert (Hreq : σR l (req (latch_input l)) = if is_token_latch l then Bit0 else Bit1).
        { unfold σR; reduce_eqb.
          repeat (compare_next; auto).
        }
        destruct l; simpl in Hreq.
        * (* Odd==not token latch *)
          apply handshake_out_of_sync.
          rewrite Hack, Hreq; auto.
        * (* Even==token latch *)
          apply handshake_in_sync.
          rewrite Hack, Hreq; auto.
      }
      { assert (Hack : σR l (ack (latch_output l)) = Bit0).
        { unfold σR; reduce_eqb; auto. }
        assert (Hreq : σR l (req (latch_output l)) = if is_token_latch l then Bit1 else Bit0).
        { unfold σR; reduce_eqb.
          repeat (compare_next; auto).
        }
        destruct l; simpl in Hreq.
        * (* Odd==not token latch *)
          apply handshake_in_sync.
          rewrite Hack, Hreq; auto.
        * (* Even==token latch *)
          apply handshake_out_of_sync.
          rewrite Hack, Hreq; auto.
      }
      { unfold σR; reduce_eqb.
        repeat (compare_next; try constructor);
          destruct l; try constructor.
      }
  Qed.




  Lemma latch_stage_well_formed : forall l, well_formed (latch_stage_with_env l).
  Proof.
    intros l.
    set (Hdisjoint := scheme_all_disjoint l).
    unfold latch_stage_with_env, left_env_component, right_env_component, latch_stage,
           latch_stage_with_reset, latch_flop_component.
    repeat match goal with
    | [ |- well_formed _] => apply wf_union; auto; try unfold space_domain
    | [ |- well_formed _ ] => apply hide_wf; auto; simpl; try solve_set
    | [ |- well_formed _ ] => apply func_wf; solve_set
    | [ |- in_dec _ ] => simpl; auto 30 with sets; fail
    | [ |- _ ⊥ _ ] => constructor; intros x Hx; simpl in *; decompose_set_structure; fail
    end.

    apply flop_wf.
    destruct l; simpl; repeat (constructor; try_solve_set).

  Qed.
  Hint Resolve latch_stage_well_formed.


Lemma union_inversion_left : forall (S1 S2 : StateSpace name) σ x v σ',
    (S1 ∥ S2) ⊢ σ →{Some (Event x v)} Some σ' ->
    x ∈ space_domain S1 ->
    S1 ⊢ σ →{Some (Event x v)} Some σ'.
Proof.
  intros ? ? ? ? ? ? Hstep Hdom.
  inversion Hstep; subst; auto.
  (* the only remaining case is when x ∉ dom(S1), a contradiction *)
  { contradict H0. constructor. auto. }
Qed.

Lemma union_inversion_right : forall (S1 S2 : StateSpace name) σ x v σ',
    (S1 ∥ S2) ⊢ σ →{Some (Event x v)} Some σ' ->
    x ∈ space_domain S2 ->
    S2 ⊢ σ →{Some (Event x v)} Some σ'.
Proof.
  intros ? ? ? ? ? ? Hstep Hdom.
  inversion Hstep; subst; auto.
  (* the only remaining case is when x ∉ dom(S2), a contradiction *)
  { contradict H0. constructor. auto. }
Qed.



  Instance internal_in_dec : forall l, in_dec (space_internal (latch_stage_with_env l)).
  Admitted.

  Instance input_in_dec : forall l, in_dec (space_input (latch_stage_with_env l)).
  Admitted.

  Instance output_in_dec : forall l, in_dec (space_output (latch_stage_with_env l)).
  Admitted.

Lemma union_internal_inversion_right : forall (S1 S2 : StateSpace name) σ x v σ',
    well_formed S1 ->
    well_formed S2 ->
    space_internal S1 ⊥ space_domain S2 ->
    space_domain S1 ⊥ space_internal S2 ->
    (S1 ∥ S2) ⊢ σ →{ Some (Event x v)} Some σ' ->
    x ∉ space_domain S2 ->
    forall y, y ∈ space_internal S2 ->
    σ' y = σ y.
Proof.
  intros ? ? ? ? ? ? Hwf1 Hwf2 Hdisj1 Hdisj2 Hstep Hx y Hy.
  inversion Hstep; subst; auto.
  * unfold state_equiv_on in H2.
    rewrite H2; auto.
    unfold space_domain; solve_set.
  * contradict H0.
    constructor.

    apply wf_space in Hstep; auto.
    simpl in Hstep.
    decompose_set_structure; unfold space_domain in *;
      try solve_set;
      try (contradict Hx; solve_set).
      apply wf_union; auto.

  * inversion H0; subst;
      inversion H4; subst;
      contradict Hx; unfold space_domain; solve_set.

Qed.

Lemma hide_inversion : forall (S : StateSpace name) σ x e σ',
    (hide x S) ⊢ σ →{Some e} Some σ' ->
    S ⊢ σ →{Some e} Some σ'.
Proof.
  intros ? ? ? ? ? Hstep.
  inversion Hstep; auto.
Qed.

Lemma func_space_output_inversion : forall I (o : name) f (σ : state name) x v σ',
    o ∉ I ->
    func_space I o f ⊢ σ →{Some (Event x v)} Some σ' ->
    x = o ->
    v = f σ.
Proof.
  intros ? ? ? ? ? ? ? Ho Hstep ?. subst.
    inversion Hstep; try find_contradiction.
    subst. auto.
Qed.

Lemma func_space_output_unstable : forall I (o : name) f σ x v σ',
    o ∉ I ->
    func_space I o f ⊢ σ →{Some (Event x v)} Some σ' ->
    x = o ->
    σ x <> v.
Proof.
    intros ? ? ? ? ? ? ? ? Hstep Heq.
    subst.
    inversion Hstep; subst; try find_contradiction; auto.
Qed.

Lemma func_space_output_neq : forall I (o : name) f σ v σ' y,
    o ∉ I ->
    func_space I o f ⊢ σ →{Some (Event o v)} Some σ' ->
    y <> o ->
    σ' y = σ y.
Proof.
  intros ? ? ? ? ? ? ? ? Hstep Hneq.
  inversion Hstep; subst; unfold update;
    compare_next; auto.
Qed.

  Ltac step_inversion_1 :=
  match goal with
  | [ Hstep : _ ⊢ _ →{ Some _ } Some _ |- _ ] =>
      apply union_inversion_left in Hstep;
          (* the left;right is that we should only succeedd here if x ∈ output(S1) *)
      [ | unfold space_domain; left; right; simpl; solve_set; fail]
  | [ Hstep : _ ⊢ _ →{ Some _ } Some _ |- _ ] =>
      apply union_inversion_right in Hstep;
          (* the left;right is that we should only succeedd here if x ∈ output(S2) *)
      [ | unfold space_domain; left; right; simpl; solve_set; fail]
  | [ Hstep : _ ⊢ _ →{ Some _ } Some _ |- _ ] =>
      apply hide_inversion in Hstep
  end.
  Ltac step_inversion_eq :=
  repeat step_inversion_1;
  match goal with
  | [ Hstep : _ ⊢ _ →{ Some _ } Some _ |- _ ] =>
      apply func_space_output_inversion in Hstep;
        [ | simpl; solve_set; fail | simpl; solve_set; fail]
  end.
  Ltac step_inversion_unstable :=
  repeat step_inversion_1;
  match goal with
  | [ Hstep : _ ⊢ _ →{ Some _ } Some _ |- _ ] =>
      eapply func_space_output_unstable in Hstep; eauto;
        [ | simpl; solve_set; fail ]
  end.




Ltac rewrite_step_inversion :=
  match goal with
    | [ Hstep : latch_stage_with_env ?l ⊢ ?σ →{ Some (Event ?x ?v)} Some ?σ' |- context[ ?σ' ?x ] ] =>
      rewrite (wf_update _ _ (latch_stage_well_formed l) _ _ _ _ Hstep)

    | [ Hstep : latch_stage_with_env ?l ⊢ ?σ →{ Some (Event ?x ?v)} Some ?σ' |- context[ ?σ' ?y ] ] =>
      rewrite (wf_scoped _ _ (latch_stage_well_formed l) _ _ _ Hstep);
        [
        | intros; inversion 1; find_contradiction
        | simpl; try (solve_set); try (simpl in *; decompose_set_structure; solve_set); fail ]
    end.

Ltac solve_wf_handshake :=
  match goal with
  | [ H : wf_handshake (?shake ?l) ?σ
    |- wf_handshake (?shake ?l) _ ] => 
    inversion H; 
      try (left;
        repeat rewrite_step_inversion;
        step_inversion_eq; auto; fail);
      try (right;
        repeat rewrite_step_inversion;
        step_inversion_eq; auto; fail);
      fail
  end.


Ltac solve_val_is_bit :=
  auto;
  repeat match goal with

  | [ |- context[ latch_to_token_flag ?l ] ] => destruct l; simpl

  | [ Hwf1 : forall x, x ∈ ?X -> val_is_bit (?σ x) |- context[?σ ?y] ] =>
    let Hwf1' := fresh "Hwf1" in
    assert (Hwf1' : val_is_bit (σ y))
      by (apply Hwf1; simpl; try unfold space_domain; solve_set);
    clear Hwf1;
    auto

  | [ H : val_is_bit (?σ ?x) |- val_is_bit (?f (?σ ?x)) ] =>
    inversion H; subst;
    auto with click

  | [ H : ?S ⊢ ?σ →{Some (Event ?x ?v)} Some ?σ' |- val_is_bit ?v ] =>
    step_inversion_eq; subst

  | [ |- val_is_bit _ ] =>
    rewrite_step_inversion
  end; fail.


  Lemma step_wf_state_lemma : forall l σ e σ',
    wf_stage_state l σ ->
    latch_stage_with_env l ⊢ σ →{Some e} Some σ' ->
    wf_stage_state l σ'.
  Proof.
    intros l σ [x v] σ' [Hwf1 Hwf2 Hwf3 Hwf4] Hstep.
    set (Hdisjoint := scheme_all_disjoint l).
    assert (Hx : x ∈ space_input (latch_stage_with_env l) ∪ space_output (latch_stage_with_env l)).
    { eapply wf_space; eauto. }
    rewrite latch_stage_with_env_input, latch_stage_with_env_output in Hx.
    rewrite latch_stage_input, latch_stage_output in Hx.

    decompose_set_structure;
    (constructor;
      [ intros y Hy;
        match goal with
        [ Hstep : latch_stage_with_env ?l ⊢ ?σ →{ Some (Event ?x _)} Some ?σ' |- _] =>
          compare y x; try solve_val_is_bit
        end
      | try solve_wf_handshake
      | try solve_wf_handshake
      | try solve_val_is_bit
      ]).

    *
      destruct (y ∈? space_internal (latch_stage_with_env l)) as [Hinternal | Hinternal].
      2:{
        rewrite (wf_scoped _ _ (latch_stage_well_formed l) _ _ _ Hstep);
        [
        | intros; inversion 1; find_contradiction
        | simpl; try (solve_set); try (simpl in *; decompose_set_structure; solve_set) ].
        solve_val_is_bit.
      }
      1:{
        (* when req (latch_input l) event occurs, no internal wires change... *)
        assert (Heq : σ' y = σ y).
        { repeat step_inversion_1.
          eapply func_space_output_neq; [ | eauto | ]; solve_set.
        }
        rewrite Heq. solve_val_is_bit.
      }

    * (* ctrl_reset_n *)
      repeat step_inversion_1.
      (* rewrite_step_inversion ??? *)
      erewrite (wf_scoped _ _ _ _ _ _ Hstep).
      2:{ intros. inversion 1; find_contradiction. }
      2:{ simpl. solve_set. }
      auto.

    * (* ack (latch_output l) *)
      destruct (y ∈? space_internal (latch_stage_with_env l)) as [Hinternal | Hinternal].
      + assert (Heq : σ' y = σ y).
        { repeat step_inversion_1.
          eapply func_space_output_neq; [ | eauto | ]; solve_set.
        }
        rewrite Heq. solve_val_is_bit.
      + rewrite (wf_scoped _ _ (latch_stage_well_formed l) _ _ _ Hstep);
        [
        | intros; inversion 1; find_contradiction
        | simpl; try (solve_set); try (simpl in *; decompose_set_structure; solve_set); fail ].
        solve_val_is_bit.

    * (* ctrl_reset_n *)
      repeat step_inversion_1.
      (* rewrite_step_inversion ??? *)
      erewrite (wf_scoped _ _ _ _ _ _ Hstep).
      2:{ intros. inversion 1; find_contradiction. }
      2:{ simpl. solve_set. }
      auto.

    * (* ack (latch_input l) *)
      destruct (y ∈? space_internal (latch_stage_with_env l)) as [Hinternal | Hinternal].
      + assert (Heq : σ' y = σ y).
        { repeat step_inversion_1.
          eapply func_space_output_neq; [ | eauto | ]; solve_set.
        }
        rewrite Heq. solve_val_is_bit.
      + rewrite (wf_scoped _ _ (latch_stage_well_formed l) _ _ _ Hstep);
        [
        | intros; inversion 1; find_contradiction
        | simpl; try (solve_set); try (simpl in *; decompose_set_structure; solve_set); fail ].
        solve_val_is_bit.



    * assert (Hstate0' :
                σ (ack (latch_input l)) = match latch_to_token_flag l with
                           | Token => σ (latch_state0 l)
                           | NonToken => neg_value (σ (latch_state0 l))
                           end).
       { assert (v_bit : val_is_bit v).
         { step_inversion_eq; subst. solve_val_is_bit. }
         assert (Hneq : σ (ack (latch_input l)) = neg_value v).
         { step_inversion_unstable.
           erewrite val_is_bit_neq; eauto.
           solve_val_is_bit.
         }

         replace v with
            (match latch_to_token_flag l with
             | Token => neg_value (σ (latch_state0 l))
             | NonToken => σ (latch_state0 l)
             end) in * by (step_inversion_eq; auto).
         rewrite Hneq.
         destruct l; simpl; auto.
         rewrite val_is_bit_neg_neg; auto; solve_val_is_bit.
       }
        inversion Hwf2.
        + right. repeat rewrite_step_inversion.
          step_inversion_eq. subst.
          rewrite H0.
          rewrite Hstate0'.
          destruct l; simpl; auto.


          rewrite val_is_bit_neg_neg; auto. solve_val_is_bit.

        + left. repeat rewrite_step_inversion.
          step_inversion_eq. subst.
          rewrite H0.
          rewrite Hstate0'.
          destruct l; simpl; auto.

          rewrite val_is_bit_neg_neg; auto. solve_val_is_bit.

    * (* ctrl_reset_n *)
      repeat step_inversion_1.
      (* rewrite_step_inversion ??? *)
      erewrite (wf_scoped _ _ _ _ _ _ Hstep).
      2:{ intros. inversion 1; find_contradiction. }
      2:{ simpl. solve_set. }
      auto.

    * (* req (latch_output l) *)
      destruct (y ∈? space_internal (latch_stage_with_env l)) as [Hinternal | Hinternal].
      + assert (Heq : σ' y = σ y).
        { repeat step_inversion_1.
          eapply func_space_output_neq; [ | eauto | ]; solve_set.
        }
        rewrite Heq. solve_val_is_bit.
      + rewrite (wf_scoped _ _ (latch_stage_well_formed l) _ _ _ Hstep);
        [
        | intros; inversion 1; find_contradiction
        | simpl; try (solve_set); try (simpl in *; decompose_set_structure; solve_set); fail ].
        solve_val_is_bit.

    * assert (Hstate0 : σ (req (latch_output l)) = neg_value (σ (latch_state0 l))).
      { replace v with (σ (latch_state0 l)) in * by (step_inversion_eq; auto).
        step_inversion_unstable.
        erewrite val_is_bit_neq; eauto; solve_val_is_bit.
      }

      inversion Hwf3.
        + right. repeat rewrite_step_inversion.
          step_inversion_eq. subst.
          rewrite <- H0.
          rewrite Hstate0.
          rewrite val_is_bit_neg_neg; auto. solve_val_is_bit.

        + left. repeat rewrite_step_inversion.
          step_inversion_eq. subst.


      apply val_is_bit_neg_inversion in H0; try solve_val_is_bit.
      rewrite <- H0.
      rewrite Hstate0.
      rewrite val_is_bit_neg_neg; auto; solve_val_is_bit.

    * (* ctrl_reset_n *)
      repeat step_inversion_1.
      (* rewrite_step_inversion ??? *)
      erewrite (wf_scoped _ _ _ _ _ _ Hstep).
      2:{ intros. inversion 1; find_contradiction. }
      2:{ simpl. solve_set. }
      auto.

    * (* latch_clk *)
      rewrite_step_inversion.
      step_inversion_eq; subst.
      unfold tok_clk_defn, clk_defn.
      assert (Hctrl : σ (@ctrl_reset_n _ _ scheme) = Num 1) by admit (* why?? *).
      assert (Hreq : val_is_bit (σ (req (latch_input l))))
        by (apply Hwf1; simpl; try unfold space_domain; solve_set).
      assert (Hack : val_is_bit (σ (ack (latch_output l))))
        by (apply Hwf1; simpl; try unfold space_domain; solve_set).
      assert (Hstate0 : val_is_bit (σ (latch_state0 l)))
        by (apply Hwf1; simpl; try unfold space_domain; solve_set).

      destruct l; simpl; rewrite Hctrl;
        inversion Hreq; subst; simpl;
        inversion Hstate0; subst; simpl;
        inversion Hack; subst; simpl; constructor.

    * (* latch_clk *)
      destruct (y ∈? space_internal (latch_stage_with_env l)) as [Hinternal | Hinternal].
      + assert (Heq : σ' y = σ y).
        { repeat step_inversion_1.
          eapply func_space_output_neq; [ | eauto | ]; solve_set.
        }
        rewrite Heq. solve_val_is_bit.
      + rewrite (wf_scoped _ _ (latch_stage_well_formed l) _ _ _ Hstep);
        [
        | intros; inversion 1; find_contradiction
        | simpl; try (solve_set); try (simpl in *; decompose_set_structure; solve_set); fail ].
        solve_val_is_bit.

    * (* ctrl_reset_n *)
      repeat step_inversion_1.
      (* rewrite_step_inversion ??? *)
      erewrite (wf_scoped _ _ _ _ _ _ Hstep).
      2:{ intros. inversion 1; find_contradiction. }
      2:{ simpl. solve_set. }
      auto.

(*
    * (* latch_clk *)
      rewrite_step_inversion.
      step_inversion_eq; subst.
      unfold tok_clk_defn, clk_defn.
      assert (Hctrl : σ (@ctrl_reset_n _ _ scheme) = Num 1) by admit (* why?? *).
      assert (Hreq : val_is_bit (σ (req (latch_input l))))
        by (apply Hwf1; simpl; try unfold space_domain; solve_set).
      assert (Hack : val_is_bit (σ (ack (latch_output l))))
        by (apply Hwf1; simpl; try unfold space_domain; solve_set).
      assert (Hstate0 : val_is_bit (σ (latch_state0 l)))
        by (apply Hwf1; simpl; try unfold space_domain; solve_set).

      destruct l; simpl; rewrite Hctrl;
        inversion Hreq; subst; simpl;
        inversion Hstate0; subst; simpl;
        inversion Hack; subst; simpl; constructor.
*)
  Admitted.


  Lemma step_wf_state_eps : forall l σ σ',
    wf_stage_state l σ ->
    latch_stage_with_env l ⊢ σ →{None} Some σ' ->
    wf_stage_state l σ'.
  Admitted.
  Lemma step_wf_state : forall l tr σ,
    latch_stage_with_env l ⊢ σR l →*{tr} Some σ ->
    wf_stage_state l σ.
  Proof.
    intros l tr σ Hstep.
    set (Hdisjoint := scheme_all_disjoint l).
    remember (Some σ) as τ; generalize dependent σ.
    induction Hstep; intros σ Hτ; subst.
    * inversion Hτ; subst.
      apply step_wf_state_σR.
    * eapply step_wf_state_lemma; eauto.
    * eapply step_wf_state_eps; eauto.
  Qed.

End WF_stage.
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
