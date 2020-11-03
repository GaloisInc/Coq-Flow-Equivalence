Require Import Base.
Require Import Circuit.
Require Import StateSpace.
Require Import Monad.

Require Import List.
Import ListNotations.
Open Scope list_scope.

Require Import Omega.


Print NameType.
Module Click (Export name : NameType).


Existing Instance name_eq_dec.
Set Implicit Arguments.


(** * Define click circuits at state spaces, building off of StateSpace.v *)

(** A handshake has two names: [req h] and [ack h]. *)
Record handshake :=
  { req : name
  ; ack : name }.

Class naming_scheme {even odd} :=
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


(*
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
*)
Section Utils.
  (** [forward x y] is the state space that updates [y] (the output) to have the
  same value as [x] (the input). *)
  Definition forward (x y : name) := func_space (x::nil) y (fun σ => σ x).
  (** [output x (Some v)] is the state space that updates [x] (the output) to
  have the value [v].

    [output x None] is the state space that simply treats [x] as an output whose
value never changes. When composed with a state space where [x] is an input,
this turns [x] from an input to an output in the union space. *)
  Definition output x (v : option value) :=
    func_space nil x (fun σ => match v with
                         | None => σ x
                         | Some v' => v'
                         end).

  (** An inverter *)
  Definition NOT x y := func_space (x::nil) y (fun σ => neg_value (σ x)).


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

(* TODO: incorporate in a way separate from Fresh monad? 
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
*)

End Split.


(** * Define an ordinary Click stage, both token and non-token variants. *)
Section Stage.
  (** 1. declare all wire names in stage : StageNames *)

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
(*  tok_clk_defn := (req i /\ state0 /\ ack o)
                 \/ (not (req i) /\ not state0 /\ not (ack o))
*)
  Definition tok_clk_defn σ :=
    match σ ctrl_reset_n, σ (req i) , σ state0 , σ (ack o) with
    | Num 0, _    , _    , _     => Num 0
    | Num 1, Num 1, Num 1, Num 1 => Num 1
    | Num 1, Num 0, Num 0, Num 0 => Num 1
    | Num 1, Num _, Num _, Num _ => Num 0
    | _    , _    , _    , _     => X
    end.
(*
  Definition clk_defn f :=
    match σ ctrl_reset_n with
    | Bit0 => Bit0
    | Bit1 => let r := σ (req i) in
              let a := σ (ack o) in
              let s := σ state0  in
              value_or (value_and 
    | _    => X
    end.
    value_and (σ
*)

  Inductive token_flag := Token | NonToken.

  Definition clk_component f := 
    func_space (state0::req i::ack o::ctrl_reset_n::nil) clk (match f with
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

  (** NOTE: added delay here *)
  Definition ack_i_output f := (*match f with
                            | Token => NOT state0 (ack i)
                            | NonToken => forward state0 (ack i)
                            end.*)
    delay_space
    (func_space (state0::nil) (ack i) (fun σ => match f with
                                                    | Token => neg_value (σ state0)
                                                    | NonToken => σ state0
                                                    end))
    (clk::nil)
    (fun σ => σ clk = Bit0)
    (fun σ => σ clk =? Bit0).

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
    constructor; intros x Hx; simpl in *;
      decompose_set_structure;
      solve_set.
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

End Click.



Module Type EOType.
  Parameter even odd : Set.
  Parameter eq_dec_even : eq_dec even.
  Parameter eq_dec_odd : eq_dec odd.
  Existing Instance eq_dec_even.
  Existing Instance eq_dec_odd.
  Existing Instance latch_eq_dec.
End EOType.

Require Import Coq.Strings.String.

Module Type ClickType.
  Declare Module eo : EOType.
  Import eo.
    Inductive click_name_type :=
    | just_nat : string -> click_name_type
    | latch_and_nat : latch even odd -> string -> click_name_type
    .
    Lemma just_nat_inj : forall a1 a2, a1 <> a2 -> just_nat a1 <> just_nat a2.
    Proof.
      intros. inversion 1. subst. contradiction.
    Qed.
    Lemma just_nat_and_latch_neq : forall a l x,
        just_nat a <> latch_and_nat l x.
    Proof. intros. inversion 1. Qed.
    Lemma latch_and_nat_inj : forall a1 a2 l1 l2, l1 <> l2 \/ a1 <> a2 ->
                                                  latch_and_nat l1 a1 <> latch_and_nat l2 a2.
    Proof.
      intros. inversion 1. subst. 
      destruct H; contradiction.
    Qed.

    Definition click_name_type_eq_dec : eq_dec click_name_type.
    Proof.
      constructor.
      intros a b.
      refine (match a, b with
              | just_nat a1, just_nat a2 =>
                if Dec a1 a2 then left _ else right _
              | just_nat _, latch_and_nat _ _ => right _
              | latch_and_nat _ _, just_nat _ => right _
              | latch_and_nat l1 x1, latch_and_nat l2 x2 =>
                if Dec x1 x2
                then if Dec l1 l2
                     then left _
                     else right _
                else right _
              end).
      { constructor. apply string_dec. }
      { f_equal. assumption. }
      { apply just_nat_inj; assumption. }
      { apply just_nat_and_latch_neq. }
      { apply not_eq_sym. apply just_nat_and_latch_neq. }
      { constructor. apply string_dec. }
      { f_equal; assumption. }
      { apply latch_and_nat_inj. left. assumption. }
      { apply latch_and_nat_inj. right. assumption. }
    Defined.

    Module Name <: NameType.
      Definition name := click_name_type.
      Instance name_eq_dec : eq_dec name := click_name_type_eq_dec.
    End Name.
    
  Export Name.

  Module click := Click(Name).
  Export click.

(*  Parameter scheme : @naming_scheme even odd.
  Existing Instance scheme.*)

  Module StateSpaceTacticsName := StateSpaceTactics(Name).
  Export StateSpaceTacticsName.

  Module Structural := Structural_SS(Name).
  Export Structural.

  Definition concrete_handshake l x y : handshake :=
  {| req := latch_and_nat l x
  ;  ack := latch_and_nat l y |}.

  Instance scheme : naming_scheme :=
  {| latch_input := fun l => concrete_handshake l "l_req" "l_ack"
   ; latch_output := fun l => concrete_handshake l "r_req" "r_ack"
   ; latch_clk := fun l => latch_and_nat l "clk"
   ; latch_state0 := fun l => latch_and_nat l "state0"
   ; latch_old_clk := fun l => latch_and_nat l "old_clk"
   ; latch_not_state0 := fun l => latch_and_nat l "not_state0"
   ; latch_hidden := fun l => latch_and_nat l "hidden"
   ; ctrl_reset_n := just_nat "ctrl_reset_n"
   ; dp_reset_n := just_nat "dp_reset_n"
   |}.
  { intros l.
    repeat constructor;
    to_in_list_dec;
    simpl;
    auto.
  }
  Defined.
  Export eo.

  Export EnsembleNotation.

(*  Module StateSpaceTacticsName := StateSpaceTactics(Name).

  Module Structural := Structural_SS(Name).
*)

End ClickType.

Module Desync (Export click_module : ClickType).
(*
  Module click_module := latch_nat_pair_ClickType(eoType).
*)
  Export click_module.
  

  Existing Instance scheme.
  Lemma latch_input_eq : forall l,
    req (latch_input l) <> req (latch_output l).
  Proof.
    intros. simpl. inversion 1.
  Abort.

(*  Variable c : circuit even odd.*)

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
    ack_i_output (latch_input l) (latch_clk l) (latch_state0 l) (latch_to_token_flag l).
  Definition latch_stage_with_reset l :=
      latch_clk_component l ∥ latch_flop_component l
    ∥ latch_left_ack_component l ∥ latch_right_req_component l.
  Definition latch_stage (l : latch even odd) :=
      hide (latch_state0 l)
    ( hide dp_reset_n
    ( hide ctrl_reset_n
    ( latch_stage_with_reset l ∥ output dp_reset_n None ∥ output ctrl_reset_n None ))).



Search (∅ ∖ _). About union_emptyset.
  Lemma union_emptyset_r : forall {X} (A : Ensemble X),
    A ∪ ∅ == A.
  Admitted.
  Lemma intersection_emptyset_r : forall {X} (A : Ensemble X),
    A ∩ ∅ == ∅.
  Admitted.
  Lemma setminus_emptyset_r : forall {X} (A : Ensemble X),
    A ∖ ∅ == A.
  Admitted.


Ltac decide_in x X :=
  match X with
  | singleton x => constr:(true)
  | singleton (match latch_to_token_flag _ with
               | Token => x
               | NonToken => _
               end) => constr:(true)
  | singleton (match latch_to_token_flag _ with
               | Token => _
               | NonToken => x
               end) => constr:(true)
  | singleton ?y => constr:(false)
  | ?X1 ∪ ?X2 => let b1 := decide_in x X1 in
                  match b1 with
                  | true => constr:(true)
                  | _ => let b2 := decide_in x X2 in
                         constr:(b2)
                  end
  | ?X1 ∖ ?X2 => let b2 := decide_in x X2 in
                 match b2 with
                 | true => constr:(false)
                 | _    => decide_in x X1
                 end
  end.

    Ltac reduce_set_simpl := match goal with
    | [ |- context[ ∅ ∩ ?A ] ] => rewrite (intersection_emptyset A)
    | [ |- context[ ?A ∩ ∅ ] ] => rewrite (intersection_emptyset_r A)
    | [ |- context[ ∅ ∖ ?A ] ] => rewrite (setminus_emptyset A)
    | [ |- context[ ?A ∖ ∅ ] ] => rewrite (setminus_emptyset_r A)
    | [ |- context[ ∅ ∪ ?A ] ] => rewrite (union_emptyset A)
    | [ |- context[ ?A ∪ ∅ ] ] => rewrite (union_emptyset_r A)
    end.

(*    do 5 match goal with
    | [ |- context [ singleton ?x ∖ ?X ] ] => let b := decide_in x X in
                                              match b with
                                              | true => rewrite (singleton_setminus_in X x);
                                                          [ | solve_set]
                                              | false => rewrite (singleton_setminus_not_in X x);
                                                          [ | solve_set]
                                              end

    | [ |- context [ ?A ∖ singleton ?x ] ] =>
      match decide_in x A with
      | false => rewrite (setminus_singleton_not_in A x);
                   [ | try solve_set; try (destruct l; solve_set) ]
      end

    | [ |- context[ (?A ∪ ?B) ∖ ?C ] ] =>  rewrite (union_setminus_distr A B C)
    end.
*)



 Lemma latch_stage_input : forall l,
    space_input (latch_stage l) == from_list [req (latch_input l);ack (latch_output l)].
  Proof.
    intro l.
    simpl.
    destruct l;
    constructor; intros x Hx; simpl in *; decompose_set_structure; solve_set.
  Qed.

  Lemma latch_stage_output : forall l,
    space_output (latch_stage l) == from_list [ack (latch_input l);req (latch_output l);latch_clk l].
  Proof.
    intro l.
    constructor; intros x Hx; simpl in *; decompose_set_structure; solve_set.
  Qed.
  Lemma latch_stage_internal : forall l,
    space_internal (latch_stage l) ==  from_list [latch_old_clk l; latch_hidden l;
                                                  latch_state0 l; latch_not_state0 l;
                                                  ctrl_reset_n; dp_reset_n].
  Proof.
    intro l.
    constructor; intros x Hx; simpl in *; decompose_set_structure; try solve_set.
  Qed.



  (** In order to add the appropriate splits and joins, we need a *function*
  that produces a list of all the right (resp. left) neighbors of a latch [l].
  This is pretty ugly currently, but could be improved. *)
(*
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
*)

  (** Produce the appropriate split and join components for a particular latch. *)
(*
  Definition neighbor_split (l : latch even odd) :=
    let ls := right_neighbors_of l c in
    split_n (latch_output l) (fmap latch_input (right_neighbors_of l c)).
  Definition neighbor_join (l : latch even odd) :=
    let ls := left_neighbors_of l c in
    join_n (fmap latch_output (left_neighbors_of l c)) (latch_input l).
*)

(*
  (** TODO: move this to a more appropriate location. *)
  Class enumerable (A : Set) :=
  { enumerate : list A
  ; enumerate_proof : forall (a : A), In a enumerate
  }.

  Arguments enumerate A : clear implicits.
  Context `{enum_even : enumerable even} `{enum_odd : enumerable odd}.
*)
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
(*
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
*)

(*
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
*)

End Desync.

(*
Module Type EvenOddType.
  Parameter even odd : Set.

  Axiom scheme : naming_scheme even odd.
  Existing Instance scheme.
End EvenOddType.
*)
Module WFStage (Export ClickModule : ClickType).
  Import click.

  Definition left_env_component (l : latch even odd) :=
    NOT (ack (latch_input l)) (req (latch_input l)).
  Definition right_env_component (l : latch even odd) :=
    forward (req (latch_output l)) (ack (latch_output l)).

  Module Desync := Desync(ClickModule).
  Import Desync.


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
    intros x Hx. simpl in Hx. decompose_set_structure;
    destruct l'; simpl in *; find_contradiction.
  Qed.
  Lemma latch_stage_with_env_output' : forall l,
    space_output (latch_stage_with_env l) == space_input (latch_stage l) ∪ space_output (latch_stage l).
  Proof.
    intros l'.
    split.
    { intros x Hx. simpl in Hx. decompose_set_structure; solve_set. }
    { intros x Hx. simpl in Hx. decompose_set_structure; try solve_set;
      destruct l'; simpl in *; find_contradiction.
    }
  Qed.

  Lemma latch_stage_with_env_output : forall l,
     space_output (latch_stage_with_env l) == from_list [ req (latch_input l); ack (latch_input l)
                                                        ; req (latch_output l); ack (latch_output l)
                                                        ; latch_clk l].
  Proof.
    intros. rewrite latch_stage_with_env_output'.
    rewrite latch_stage_input, latch_stage_output.
    split; intros x Hx; decompose_set_structure; solve_space_set.
  Qed.

  Lemma latch_stage_with_env_internal' : forall l,
    space_internal (latch_stage_with_env l) == space_internal (latch_stage l).
  Proof.
    intros l'.
    split.
    { intros x Hx. simpl in Hx. decompose_set_structure;
      destruct l'; simpl in *; find_contradiction.
    }
    { intros x Hx. simpl in Hx. decompose_set_structure; try solve_set;
      destruct l'; simpl in *; find_contradiction.
    }
  Qed.

  Lemma latch_stage_with_env_internal : forall l,
    space_internal (latch_stage_with_env l) == from_list
      [latch_old_clk l; latch_hidden l; latch_state0 l; latch_not_state0 l; ctrl_reset_n; dp_reset_n].
  Proof.
    intros l.
    rewrite latch_stage_with_env_internal'.
    rewrite latch_stage_internal.
    reflexivity.
  Qed.

  Lemma dom_latch_stage_with_env : forall l,
    space_domain (latch_stage_with_env l) ==
       from_list [req (latch_input l); ack (latch_output l)
                 ; ack (latch_input l); req (latch_output l); latch_clk l
                 ; latch_state0 l; latch_not_state0 l; latch_old_clk l
                 ; latch_hidden l; ctrl_reset_n; dp_reset_n
                 ].
  Proof.
    intros l'.
    unfold space_domain.
    rewrite latch_stage_with_env_input.
    rewrite latch_stage_with_env_output.
    rewrite latch_stage_with_env_internal.
    split; intros x Hx; decompose_set_structure; solve_space_set.
  Qed.



  Hint Constructors val_is_bit : click.
  Inductive wf_handshake (h : handshake) (σ : state name) : Prop :=
  | handshake_in_sync : σ (req h) = σ (ack h) -> wf_handshake h σ
  | handshake_out_of_sync : σ (req h) = neg_value (σ (ack h)) -> wf_handshake h σ.
  Record wf_stage_state (l : latch even odd) (σ : state name) : Prop :=
    { wf_all_bits : forall x, x ∈ space_domain (latch_stage_with_env l) -> val_is_bit (σ x)
(*    ; wf_latch_input  : wf_handshake (latch_input l)  σ
    ; wf_latch_output : wf_handshake (latch_output l) σ
*)
    ; wf_ctrl_reset_n : σ ctrl_reset_n = Bit1
    ; wf_dp_reset_n : σ dp_reset_n = Bit1
    ; wf_hidden : σ (latch_hidden l) = Bit1
(*
    ; wf_flop_stable  : ~ stable (latch_flop_component l) σ ->
                              stable (latch_clk_component l) σ
                           /\ stable (latch_left_ack_component l) σ
                           /\ stable (latch_right_req_component l) σ
    ; wf_clk_stable   : ~ stable (latch_clk_component l) σ ->
                              stable (latch_flop_component l) σ
                           /\ stable (latch_left_ack_component l) σ
                           /\ stable (latch_right_req_component l) σ
*)
    ; wf_left_ack_stable  : ~ stable (latch_left_ack_component l) σ ->
                              stable (latch_flop_component l) σ

    ; wf_right_req_stable : ~ stable (latch_right_req_component l) σ ->
                              stable (latch_flop_component l) σ

    ; wf_clk_unstable : σ (latch_state0 l) = σ (latch_not_state0 l) ->
                        σ (latch_clk l) = σ (latch_old_clk l)
                        


    }.

Lemma val_is_bit_wf_handshake : forall σ h,
    val_is_bit (σ (req h)) ->
    val_is_bit (σ (ack h)) ->
    wf_handshake h σ.
Proof.
    intros σ h Hreq Hack.
    inversion Hreq as [Hreq' | Hreq']; inversion Hack as [Hack' | Hack'].
    Print wf_handshake.
    apply handshake_in_sync; rewrite <- Hreq', <- Hack'; auto.
    apply handshake_out_of_sync; rewrite <- Hreq', <- Hack'; auto.
    apply handshake_out_of_sync; rewrite <- Hreq', <- Hack'; auto.
    apply handshake_in_sync; rewrite <- Hreq', <- Hack'; auto.
Qed.

  Lemma wf_latch_input : forall l σ, wf_stage_state l σ -> wf_handshake (latch_input l) σ.
  Proof.
    intros.
    apply val_is_bit_wf_handshake;
      eapply wf_all_bits; eauto.
    * rewrite dom_latch_stage_with_env.
      to_in_list_dec.
      simpl.
      reduce_eqb; auto.
    * rewrite dom_latch_stage_with_env.
      to_in_list_dec.
      simpl.
      reduce_eqb; auto.
  Qed.
  Lemma wf_latch_output : forall l σ, wf_stage_state l σ -> wf_handshake (latch_output l) σ.
  Proof.
    intros.
    apply val_is_bit_wf_handshake;
      eapply wf_all_bits; eauto.
    * rewrite dom_latch_stage_with_env.
      to_in_list_dec.
      simpl.
      reduce_eqb; auto.
    * rewrite dom_latch_stage_with_env.
      to_in_list_dec.
      simpl.
      reduce_eqb; auto.
  Qed.

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
      { unfold σR; repeat compare_next; constructor. }
      { unfold σR. repeat compare_next; try constructor. }
      { unfold σR. repeat compare_next; try constructor. }

      { admit (*TODO *). }
      { admit (*TODO *). }

      { unfold σR. simpl. reduce_eqb. }
  Admitted.

Ltac solve_all_disjoint :=
  repeat match goal with
  | [ |- all_disjoint _ ] => repeat constructor; try solve_set
  | [ l : latch _ _ |- ?x ∈ ?X ] => destruct l; solve_set
  | [ l : latch _ _ |- ?x ∉ ?X ] => destruct l; solve_set
  end.
Ltac solve_wf :=
    repeat match goal with
    | [ |- well_formed _ ] => auto; fail
    | [ |- well_formed (_ ∥ _)] => apply wf_union; auto; try unfold space_domain
    | [ |- well_formed (hide _ _) ] => apply hide_wf; auto; try solve_space_set
    | [ |- well_formed (func_space _ _ _) ] => apply func_wf; try (to_in_list_dec; auto; fail)
    | [ |- well_formed (output _ _) ] => apply func_wf; try (to_in_list_dec; auto; fail)
    | [ |- well_formed (NOT _ _) ] => apply func_wf; try (to_in_list_dec; auto; fail)
    | [ |- well_formed (flop _ _ _ _ _ _) ] => apply flop_wf; solve_all_disjoint
    | [ |- well_formed (delay_space _ _ _ _) ] => apply delay_space_wf
    | [ |- in_dec _ ] => typeclasses eauto
    | [ |- _ ⊥ _ ] => constructor; try unfold space_domain; intros x Hx; simpl in *; decompose_set_structure; fail
    end. 


  Lemma latch_clk_component_well_formed : forall l,  well_formed (latch_clk_component l).
  Proof.
    intros l. unfold_StateSpace (latch_clk_component l).
    solve_wf.
  Qed.
  Lemma latch_flop_component_well_formed : forall l,  well_formed (latch_flop_component l).
  Proof.
    intros l. unfold_StateSpace (latch_flop_component l).
    solve_wf.
  Qed.
  Lemma latch_left_ack_component_well_formed : forall l,  well_formed (latch_left_ack_component l).
  Proof.
    intros l.
    unfold_StateSpace (latch_left_ack_component l).
    solve_wf.
    Unshelve.
    Print latch_left_ack_component.
    Print ack_i_output.
    exact (fun σ => σ (latch_clk l) =? Bit0).
  Qed.
  Lemma latch_right_req_component_well_formed : forall l,  well_formed (latch_right_req_component l).
  Proof.
    intros l. unfold_StateSpace (latch_right_req_component l).
    solve_wf.
  Qed.
  Hint Resolve latch_clk_component_well_formed latch_flop_component_well_formed
               latch_left_ack_component_well_formed latch_right_req_component_well_formed.
  Lemma latch_stage_with_reset_well_formed : forall l,  well_formed (latch_stage_with_reset l).
  Proof.
    intros. unfold latch_stage_with_reset.
    solve_wf.
  Qed.
  Hint Resolve latch_stage_with_reset_well_formed.

  Lemma latch_stage_well_formed' : forall l, well_formed (latch_stage l).
  Proof.
    intros.
    unfold latch_stage, output.
    solve_wf; simpl; try solve_set.
  Qed.
  Lemma left_env_well_formed : forall l, well_formed (left_env_component l).
  Proof. intros; unfold_StateSpace (left_env_component l).
         solve_wf.
  Qed.
  Lemma right_env_well_formed : forall l, well_formed (right_env_component l).
  Proof.  intros; unfold_StateSpace (right_env_component l).
          solve_wf.
  Qed.
  Hint Resolve left_env_well_formed right_env_well_formed latch_stage_well_formed'.



  Lemma latch_stage_well_formed : forall l, well_formed (latch_stage_with_env l).
  Proof.
    intros l.
    unfold latch_stage_with_env.
    solve_wf.
  Qed.
  Hint Resolve latch_stage_well_formed.


  Module ClickTactics.

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


  (* Depends on wf_stage_state *)
  Ltac solve_val_is_bit :=
  auto;
  repeat match goal with

  | [ H : wf_stage_state ?l ?σ |- val_is_bit (?σ ?x) ] =>
    apply (wf_all_bits H); solve_space_set

  | [ |- context[ latch_to_token_flag ?l ] ] => destruct l; simpl

  | [ Hwf1 : forall x, x ∈ space_domain ?S -> val_is_bit (?σ x) |- context[?σ ?y] ] =>
    let Hwf1' := fresh "Hwf1" in
    assert (Hwf1' : val_is_bit (σ y))
      by (apply Hwf1; try (unfold_StateSpace S);
          solve_space_set);
    clear Hwf1;
    auto

  | [ Hwf1 : forall x, x ∈ ?X -> val_is_bit (?σ x) |- context[?σ ?y] ] =>
    let Hwf1' := fresh "Hwf1" in
    assert (Hwf1' : val_is_bit (σ y))
      by (apply Hwf1; simpl; solve_space_set);
    clear Hwf1;
    auto

  | [ |- val_is_bit (?f (?σ ?x)) ] =>
    let Hbit := fresh "Hbit" in
    assert (Hbit : val_is_bit (σ x)) by solve_val_is_bit;
    inversion Hbit; subst;
    auto with click

(*
  | [ H : ?S ⊢ ?σ →{Some (Event ?x ?v)} Some ?σ' |- val_is_bit ?v ] =>
    step_inversion_eq; subst*)

  | [ |- val_is_bit _ ] =>
    rewrite_step_inversion
  end; fail.

(*
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
*)

  Ltac decide_in_list_dec Hdec x l :=
  let b := fresh "b" in
  evar (b : bool);
  assert (Hdec : in_list_dec x l = b);
  [ simpl;
    try match goal with
    (* this is useful to compare types *)
    | [ |- context[ latch_to_token_flag ?latch ] ] => destruct latch; simpl
    end;
    repeat compare_next;
    unfold b;
    reflexivity
  | unfold b in Hdec; clear b
  ].

  Ltac step_inversion Hstep :=
  match type of Hstep with
  | ?S ⊢ _ →{_} _ =>
    unfold_StateSpace_1 S in Hstep
  end;
  match type of Hstep with
  (* Union *)
  | (?S1 ∥ ?S2) ⊢ _ →{None} _ => 
    let Hequiv := fresh "Hequiv" in
    apply union_inversion_None in Hstep;
    destruct Hstep as [[Hstep Hequiv] | [Hstep Hequiv]]

  | (?S1 ∥ ?S2) ⊢ _ →{?e} _ =>

    match goal with
    | [ He1 : event_in (space_domain S1) ?e
      , He2 : ~ event_in (space_domain S2) ?e
      |- _ ] =>
      apply union_inversion_left_only in Hstep; auto;
      let Hequiv := fresh "Hequiv" in
      destruct Hstep as [Hstep Hequiv]

    | [ He1 : ~ event_in (space_domain S1) ?e
      , He2 : event_in (space_domain S2) ?e
      |- _ ] =>
      apply union_inversion_right_only in Hstep; auto;
      let Hequiv := fresh "Hequiv" in
      destruct Hstep as [Hstep Hequiv]

    | [ He1 : event_in (space_domain S1) ?e
      , He2 : event_in (space_domain S2) ?e
      |- _ ] =>
      let Hstep1 := fresh "Hstep1" in
      let Hstep2 := fresh "Hstep2" in
      apply union_inversion_lr in Hstep;
        [ destruct Hstep as [Hstep1 Hstep2]
        | unfold space_domain; simpl; try solve_set;
          (* just in case we're blocked by a latch *)
          match goal with
          | [ |- context[ latch_to_token_flag ?l ] ] =>
            destruct l; simpl; solve_set
          end
        ]
    end

  (* Hide *)
  | hide ?x0 ?S0 ⊢ _ →{Some _} _ => apply hide_inversion in Hstep
  | hide ?x0 ?S0 ⊢ _ →{None} _ => apply hide_inversion_None in Hstep;
              let v := fresh "v" in
              destruct Hstep as [Hstep | [v Hstep]]

  (* DelaySpace *)
  | delay_space ?S0 ?sensitivities ?guard ?guardb ⊢ _ →{_} _ =>
    let Hequiv := fresh "Hequiv" in
    let Hguard := fresh "Hguard" in
    apply delay_space_inversion in Hstep;
    [ destruct Hstep as [Hstep [Hequiv Hguard]]

    | try solve_set
    ]

  (* func_space *)
  | func_space ?I ?o ?f ⊢ _ →{_} _ =>
    apply func_space_inversion in Hstep;
    [ | to_in_list_dec; simpl; repeat (auto; try compare_next); fail ];
    match type of Hstep with
    | False => contradiction
    | _ /\ _ => let Hequiv := fresh "Hequiv" in
                let Heq := fresh "Heq" in
                destruct Hstep as [Hequiv Heq];
                simpl in Heq;
                try match type of Heq with
                | ?x = ?x -> _ => specialize (Heq eq_refl)
                | ?x = ?y -> _ => clear Heq (* too much?? *)
                end
    end
  end.
About not_in_implies_event_not_in.

Ltac decide_event_in_domain e S :=
  match e with
  | None => assert (~ (@event_in name value (space_domain S) None))
              by inversion 1
  | Some (Event ?x ?v) =>
      let Hdom  := fresh "Hdom" in
      let Hdec0 := fresh "Hdec0" in
(*      let Hdec  := fresh "Hdec" in*)
      space_domain_to_list Hdom S;
      match type of Hdom with
      | (space_domain ?S == from_list ?l) =>
        decide_in_list_dec Hdec0 x l;
        from_in_list_dec
(*        rewrite <- Hdom in Hdec0*) (* doesn't work for some reason? *)
      end;
      match type of Hdec0 with
      | _ ∈ _ => apply (in_implies_event_in _ _ _ v) in Hdec0
      | _ ∉ _ => apply (@not_in_implies_event_not_in _ _ _ v) in Hdec0
      end;
      rewrite <- Hdom in Hdec0;
      clear Hdom
  end.

  Ltac decide_events_of Hstep :=
  match type of Hstep with
  | ?S ⊢ _ →{?e} Some _ => unfold_StateSpace_1 S in Hstep
  end;
  match type of Hstep with
  | (?S1 ∥ ?S2) ⊢ _ →{?e} Some _ =>
    decide_event_in_domain e S1;
    decide_event_in_domain e S2

(*
  | (?S1 ∥ ?S2) ⊢ _ →{?e} _ =>
    let He1 := fresh "He1" in 
    let He2 := fresh "He2" in 
    destruct (decide_event_in e (space_domain S1)) as [He1 | He1];
      try find_event_contradiction;
    destruct (decide_event_in e (space_domain S2)) as [He2 | He2];
      try find_event_contradiction
*)
  end.

  Ltac step_inversion_1 := match goal with
  | [ Hstep : hide _ _ ⊢ _ →{_} _ |- _ ] =>
    step_inversion Hstep
  | [ Hstep : func_space ?I ?o ?f ⊢ _ →{_} _ |- _ ] =>
    step_inversion Hstep
  | [ Hstep : delay_space _ _ _ _ ⊢ _ →{_} _ |- _ ] =>
    step_inversion Hstep
  | [ Hstep : (?S1 ∥ ?S2) ⊢ _ →{None} _ |- _ ] =>
    step_inversion Hstep
  | [ Hstep : (?S1 ∥ ?S2) ⊢ _ →{_} _ |- _ ] =>
    decide_events_of Hstep;
    step_inversion Hstep;
    repeat match goal with
    | [ He : event_in _ _ |- _ ] => clear He
    | [ He : ~ event_in _ _ |- _ ] => clear He
    end

  | [ Hstep : ?S ⊢ _ →{_} _ |- _ ] =>
    unfold_StateSpace_1 S in Hstep
  end.

  Lemma combine_state_equiv_on_domain : forall (S1 S2 : StateSpace name) σ σ',
    state_equiv_on (space_domain S1) (Some σ) (Some σ') ->
    state_equiv_on (space_domain S2) (Some σ) (Some σ') ->
    state_equiv_on (space_domain (S1 ∥ S2)) (Some σ) (Some σ').
  Proof.
    intros S1 S2 σ σ' Hequiv1 Hequiv2.
    intros x Hx.
    Search space_domain union.
    unfold space_domain in Hx; simpl in Hx.
    decompose_set_structure;
    try (rewrite <- Hequiv1; auto;
           unfold space_domain; solve_set);
    try (rewrite <- Hequiv2; auto;
           unfold space_domain; solve_set).
  Qed.

  Lemma state_equiv_on_disjoint : forall (X1 X2 : list name) σ1 σ2 σ',
    state_equiv_on (from_list X1) (Some σ1) σ' ->
    state_equiv_on (from_list X2) (Some σ2) σ' ->
    state_equiv_on (from_list X1 ∩ from_list X2) (Some σ1) (Some σ2) ->
    state_equiv_on (from_list X1 ∪ from_list X2) (Some (fun x => if in_list_dec x X1 then σ1 x else σ2 x)) σ'.
  Proof.
    intros X1 X2 σ1 σ2 τ Hequiv1 Hequiv2 Hequiv.
    destruct τ as [σ' | ]; [ | inversion Hequiv1].
    intros y Hy.
    destruct (y ∈? from_list X1) as [H1 | H1].
    { to_in_list_dec; rewrite H1.
      from_in_list_dec. rewrite <- Hequiv1; auto.
    }
    { to_in_list_dec. rewrite H1.
      from_in_list_dec. 
      decompose_set_structure.
    }
  Qed.

  
  Lemma combine_state_equiv_on : forall (X1 X2 : Ensemble name) σ σ',
    state_equiv_on X1 (Some σ) (Some σ') ->
    state_equiv_on X2 (Some σ) (Some σ') ->
    state_equiv_on (X1 ∪ X2) (Some σ) (Some σ').
  Proof.
    intros X1 X2 σ σ' H1 H2.
    intros x Hx.
    decompose_set_structure.
  Qed.

    

Ltac combine_state_equiv_on :=
  match goal with
(*
  | [ H1 : state_equiv_on (space_domain ?S1) (Some ?σ) (Some ?σ')
    , H2 : state_equiv_on (space_domain ?S2) (Some ?σ) (Some ?σ')
    |- _ ] =>
    let Hequiv := fresh "Hequiv" in
    assert (Hequiv : state_equiv_on (space_domain (S1 ∥ S2)) (Some σ) (Some σ'));
    [ apply combine_state_equiv_on_domain; auto
    | clear H1 H2 ]
*)
  | [ H1 : state_equiv_on ?X1 (Some ?σ) (Some ?σ')
    , H2 : state_equiv_on ?X2 (Some ?σ) (Some ?σ')
    |- _ ] =>
    let Hequiv := fresh "Hequiv" in
    assert (Hequiv : state_equiv_on (X1 ∪ X2) (Some σ) (Some σ'));
    [ apply combine_state_equiv_on; auto
    | clear H1 H2 ]

  end.



  End ClickTactics.
  Export ClickTactics.

  Existing Instance singleton_enumerable.
  Existing Instance empty_enumerable.
  Existing Instance from_list_enumerable.
  Instance stage_functional : forall l, functional_step_relation _ (latch_stage_with_env l).
  Proof.
    intros l.
    set (Hdisjoint := scheme_all_disjoint l).
    unfold latch_stage_with_env.
    repeat match goal with
    | [ |- functional_step_relation _ _ ] => apply union_functional
    | [ |- functional_step_relation _ _ ] => apply func_functional
    | [ |- functional_step_relation _ _ ] => apply hide_functional
    | [ |- functional_step_relation _ _ ] => apply delay_space_functional
    | [ |- functional_step_relation _ _ ] => apply flop_functional;
        repeat constructor; try solve_set;
                            try (destruct l; solve_set)
    | [ |- eq_dec _ ] => typeclasses eauto
    | [ |- in_dec _ ] => typeclasses eauto
    | [ |- enumerable _ ] => typeclasses eauto
    end.
  Defined.
  Instance stage_functional_correct : forall l,
    functional_step_relation_correct _ (latch_stage_with_env l).
  Proof.
    intros l.
    set (Hdisjoint := scheme_all_disjoint l).
    unfold latch_stage_with_env.
    repeat match goal with
    | [ |- functional_step_relation_correct _ _ ] => apply union_functional_correct
    | [ |- functional_step_relation_correct _ _ ] => apply func_functional_correct
    | [ |- functional_step_relation_correct _ _ ] => apply hide_functional_correct
    | [ |- functional_step_relation_correct _ _ ] => apply flop_functional_correct
    | [ |- functional_step_relation_correct _ _ ] => apply delay_space_functional_correct

    | [ |- well_formed _] => solve_wf
    | [ |- in_dec _ ] => typeclasses eauto
    | [ |- eq_dec _ ] => typeclasses eauto
    | [ |- _ ⊥ _ ] => try unfold space_domain; simpl; solve_set
    | [ |- _ ∈ _ ] => solve_set
    | [ |- _ ∉ _ ] => solve_set
    | [ |- _ ⊥ _ ] => constructor; intros x Hx; simpl in *; decompose_set_structure; fail
    end.
    { solve_all_disjoint. }
    { (* well-formed *)
      intros σ. split; intros Heq;
      compare_next; auto.
    }
  Qed.
(*  Admitted (* true but slow *).*)


(*
Definition decide_event_in (e : option (event name value)) (X : Ensemble name) `{in_dec _ X}
    : { event_in _ X e } + {~ (event_in _ X e)}.
Proof.
  destruct e as [[x v] | ].
  { destruct (x ∈? X) as [Hx | Hx].
    { left. constructor. auto. }
    { right. inversion 1; subst. contradict Hx; auto. }
  }
  { right. inversion 1. }
Defined.
About decide_event_in.
Arguments decide_event_in e X {H}.
*)

  Module Structural := Structural_SS(Name).
  Import Structural.



Definition latch_stage_with_env_ISpace (l : latch even odd) : ISpace.
Proof.
  set (S := latch_stage_with_env l).
  let S' := eval unfold latch_stage_with_env,
                        left_env_component, latch_stage, right_env_component,
                        latch_stage_with_reset,
                        latch_clk_component, latch_flop_component,
                        latch_left_ack_component, latch_right_req_component,
                        clk_component, flop_component, ack_i_output,
                        output, forward, NOT
    in (latch_stage_with_env l) in
  let S'' := reflect_ISpace S' in
  exact S''.
Defined.

Import StateSpace.


Add Parametric Morphism : event_in
  with signature Same_set name ==> @eq (option (event name value)) ==> iff as event_in_equiv.
Proof.
  intros X Y Hequiv e.
  split; intros Hin; inversion Hin; subst; constructor; rewrite Hequiv in *; auto.
Qed.

  Ltac combine_state_equiv_on_complex :=
  match goal with
  | [ H1 : state_equiv_on (from_list ?X1) (Some ?σ1) (Some ?σ')
    , H2 : state_equiv_on (from_list ?X2) (Some ?σ2) (Some ?σ')
    |- _ ] =>
    let Hequiv := fresh "Hequiv" in
    assert (Hequiv : state_equiv_on (from_list X1 ∪ from_list X2)
                                    (Some (fun x => if in_list_dec x X1 then σ1 x else σ2 x))
                                    (Some σ'));
    [ | clear H1 H2 ]
  end. 
Lemma not_in_intersection : forall (x : name) A B, x ∉ A \/ x ∉ B -> x ∉ (A ∩ B).
Admitted.


  Add Parametric Morphism : (state_equiv_on)
    with signature (Same_set name) ==> eq ==> eq ==> iff
    as equiv_on_iff.
  Proof.
    intros X Y Heq τ1 τ2.
    split; intros Hequiv;
    destruct τ1; destruct τ2; auto.
    * intros y Hy; rewrite <- Heq in Hy; auto.
    * intros y Hy; rewrite -> Heq in Hy; auto.
  Qed.

  Ltac standardize_state_equiv_on_set H :=
      match type of H with
      | state_equiv_on ?X _ _ =>
        let HX := fresh "HX" in
        set_to_list HX X;
        rewrite HX in H;
        clear HX
      end.

Require Import Coq.Program.Equality.

  Lemma flop_not_stable_old_clk : forall l σ,
    wf_stage_state l σ ->
    σ (latch_clk l) <> σ (latch_old_clk l) ->
    ~ stable (latch_flop_component l) σ.
  Proof.
    intros l σ Hwf Hneq.
    assert (Hclk : val_is_bit (σ (latch_clk l))).
    { eapply wf_all_bits; eauto.
      rewrite dom_latch_stage_with_env. solve_space_set. }
    assert (Hstate0 : val_is_bit (σ (latch_state0 l))).
    { eapply wf_all_bits; eauto.
      rewrite dom_latch_stage_with_env. solve_space_set. }
    assert (Hnot_state0 : val_is_bit (σ (latch_not_state0 l))).
    { eapply wf_all_bits; eauto.
      rewrite dom_latch_stage_with_env. solve_space_set. }
    dependent destruction Hclk; rename x into Hclk.
    { (* clk = 0 *)
      assert (Hstep : latch_flop_component l ⊢ σ →{None}
                        Some (update σ (latch_old_clk l) (σ (latch_clk l)))).
      { apply Hide_Neq; [ | inversion 1].
        apply Hide_Neq; [ | inversion 1].
        apply union_step_1; [inversion 1 | | ].
        2:{ unfold space_domain; simpl.
            intros x Hx; decompose_set_structure.
        }
        apply union_step_1; [inversion 1 | | ].
        2:{ unfold space_domain; simpl.
            intros x Hx; decompose_set_structure.
        }
        apply Flop_clk_fall; auto.
        { rewrite <- Hclk. congruence. }
        { intros ? ?; auto. }
      }
      intros [_ Hstable]. specialize (Hstable _ _ Hstep).
      inversion Hstable.
    }

    (* INVARIANT: If latch_clk <> latch_old_clk,
                  then latch_state0 <> latch_not_state0,
       and if latch_state0 = latch_not_state0
           then latch_clk = latch_old_clk
     *)
    assert (invariant : σ (latch_state0 l) <> σ (latch_not_state0 l)).
    { Print wf_stage_state.
      intros Heq.
      apply wf_clk_unstable in Heq; auto.
    }

    { (* clk = 1 *)

      set (H_hidden := wf_hidden _ _ Hwf).
      set (H_dp := wf_dp_reset_n _ _ Hwf).
      simpl in H_hidden, H_dp.


      assert (Hstep : latch_flop_component l ⊢ σ
                        →{Some (Event (latch_state0 l) (σ (latch_not_state0 l)))}
                        (Some (update (update σ (latch_state0 l) (σ (latch_not_state0 l)))
                                      (latch_old_clk l) (σ (latch_clk l))))).
      { apply Hide_Neq; [ | inversion 1; subst; contradict pf; solve_space_set].
        apply Hide_Neq; [ | inversion 1; subst; contradict pf; solve_space_set].
        apply union_step_1.
        { inversion 1; subst; contradict pf. unfold space_domain. simpl.
          solve_space_set.
        }
        2:{ unfold space_domain; simpl.
            intros x Hx; decompose_set_structure.
        }
        apply union_communicate.
        { apply driven_by_1.
          { constructor. simpl. solve_space_set. }
          { constructor. simpl. solve_space_set. }
        }
        2:{ apply func_input_stable.
            { solve_space_set. }
            { apply val_is_bit_neq in invariant; auto. }
            { intros x Hx. unfold update.
              decompose_set_structure.
            }
        }

        apply Flop_clk_rise; auto.
        { destruct l; simpl; auto. }
        { destruct l; simpl; auto. }
        { rewrite <- Hclk in Hneq. auto. }
        { intros ? ?; auto. }
      }
      intros [_ Hstable].
      specialize (Hstable _ _ Hstep).
      inversion Hstable; subst.
      contradict pf. simpl.
      destruct l; solve_set.
    }
  Qed.

Lemma bit_neq_neg_r : forall v, val_is_bit v ->
    v <> neg_value v.
Proof.
    intros v Hv.
    inversion Hv; subst; simpl; discriminate.
Qed.
Lemma bit_neq_neg_l : forall v, val_is_bit v ->
    neg_value v <> v.
Proof.
    intros v Hv.
    inversion Hv; subst; simpl; discriminate.
Qed.


  Lemma flop_not_stable_state : forall l σ,
    wf_stage_state l σ ->
    σ (latch_state0 l) = σ (latch_not_state0 l) ->
    ~ stable (latch_flop_component l) σ.
  Proof.
    intros l σ Hwf Heq.
    (* INVARIANT (see above):
                  if latch_state0 = latch_not_state0
                  then latch_clk = latch_old_clk
    *)

    assert (Hclk : σ (latch_clk l) = σ (latch_old_clk l)).
    { apply wf_clk_unstable; auto. }

    (* if equal, then latch_not_state0 can step *)
    assert (Hstep : latch_flop_component l ⊢ σ →{None}
                      Some (update σ (latch_not_state0 l)
                                     (neg_value (σ (latch_state0 l))))).
    { eapply Hide_Eq.
      apply Hide_Neq.
      apply union_step_1.
      { inversion 1; subst. contradict pf. unfold space_domain. simpl. solve_space_set.
      }
      apply union_communicate.
      { apply driven_by_2; constructor; simpl; solve_space_set. 
        destruct l; auto.
      }
      2:{ apply func_output.
          { rewrite <- Heq. rewrite Heq. apply bit_neq_neg_r.
            { eapply wf_all_bits; eauto.
              rewrite dom_latch_stage_with_env. solve_space_set.
            }
          }
          { reflexivity. }
          { intros x Hx. reflexivity. }
      }
      { apply Flop_input; [ | solve_space_set; destruct l; auto | intros ? ?; auto].
        left.
        set (H_hidden := wf_hidden _ _ Hwf).
        set (H_dp := wf_dp_reset_n _ _ Hwf).
        destruct l; simpl; auto;
        simpl in H_hidden, H_dp; rewrite H_dp, H_hidden; simpl;
        split; auto.
      }
      { intros x Hx.
        unfold space_domain in Hx. simpl in Hx.
        decompose_set_structure.
      }
      { inversion 1; subst.
        contradict pf. solve_space_set.
      }
    }
    intros [_ Hstable].
    specialize (Hstable _ _ Hstep).
    inversion Hstable.

  Qed.


  Lemma step_wf_state_lemma : forall l σ e σ',
    wf_stage_state l σ ->
    latch_stage_with_env l ⊢ σ →{Some e} Some σ' ->
    wf_stage_state l σ'.
  Proof.
    intros l σ [x v] σ' [Hwf1 Hwf2 Hwf3 Hwf4] Hstep.
    assert (Hx : x ∈ space_input (latch_stage_with_env l) ∪ space_output (latch_stage_with_env l)).
    { eapply wf_space; eauto. }
    rewrite latch_stage_with_env_input, latch_stage_with_env_output in Hx.
    simpl in Hx.

    decompose_set_structure.

    * (* x = l_req *)
      repeat (step_inversion_1; try combine_state_equiv_on).

      standardize_state_equiv_on_set Hequiv1.
      standardize_state_equiv_on_set Hequiv2.

      match type of Hequiv2 with
      | state_equiv_on ?X _ _ =>
        assert (HX : X == from_list [dp_reset_n; ctrl_reset_n; latch_hidden l
                                    ; latch_clk l; latch_old_clk l
                                    ; latch_state0 l; latch_not_state0 l
                                    ; ack (latch_input l); req (latch_output l); ack (latch_output l)])
      end.
      { split; intros z Hz; to_in_list_dec; simpl; simpl in Hz;    
          repeat (compare_next; auto).
        destruct l; simpl in *; find_contradiction.
        destruct l; simpl in *; find_contradiction.
      }
      rewrite HX in *; clear HX.

      combine_state_equiv_on_complex.
      { apply state_equiv_on_disjoint; auto.
        intros z Hz. unfold update. compare_next; auto.
        contradict Hz.
        apply not_in_intersection.
        left.
        destruct l; simpl; solve_set.
      }
      standardize_state_equiv_on_set Hequiv.

      match goal with
      | [ Hequiv : state_equiv_on ?X _ _ |- _ ] =>
        assert (HX : X == space_domain (latch_stage_with_env l))
      end.
      { rewrite dom_latch_stage_with_env. clear Hequiv.
        split; intros z Hz; to_in_list_dec;
          simpl; simpl in Hz;
          repeat (compare_next; auto).
      }
      rewrite HX in Hequiv. clear HX.
      
(*
      assert (H_val_is_bit : forall x0 : name, x0 ∈ space_domain (latch_stage_with_env l) ->
                             val_is_bit (σ' x0)).
      {
        intros y HY.
        rewrite_state_equiv; auto.
        simpl. repeat compare_next; auto.
        solve_val_is_bit.
      }
*)
      constructor.
      +  (* val_is_bit *)
        intros y HY.
        rewrite_state_equiv; auto.
        simpl. repeat compare_next; auto.
        solve_val_is_bit.

      + (* ctrl_reset_n *)
        rewrite_state_equiv; auto.
        { rewrite dom_latch_stage_with_env. to_in_list_dec. auto. }

      + (* dp_reset_n *)
        rewrite_state_equiv; auto.
        { rewrite dom_latch_stage_with_env. to_in_list_dec. auto. }

      + (* latch_hidden *)
        rewrite_state_equiv; auto.
        2:{ rewrite dom_latch_stage_with_env. to_in_list_dec. simpl. reduce_eqb. auto. }
        simpl. reduce_eqb. auto.

      + intros Hstable.
        split; auto.
        intros ? ? Hstep.
        repeat step_inversion_1.
        admit  (* stronger hide inversion when we don't know the result in τ?? *).
    
      + Search stable latch_flop_component.
        intros H_not_stable.
        admit.
      + (* latch_clk vs latch_state0 *)
        rewrite dom_latch_stage_with_env in Hequiv.
        rewrite_state_equiv; [ simpl; try reduce_eqb | solve_space_set ].
        rewrite_state_equiv; [ simpl; try reduce_eqb | solve_space_set ].
        rewrite_state_equiv; [ simpl; try reduce_eqb | solve_space_set ].
        rewrite_state_equiv; [ simpl; try reduce_eqb | solve_space_set ].
        auto.

    * (* r_ack *)
      repeat (step_inversion_1; try combine_state_equiv_on).

      standardize_state_equiv_on_set Hequiv1.
      standardize_state_equiv_on_set Hequiv2.

      match type of Hequiv2 with
      | state_equiv_on ?X _ _ =>
        assert (HX : X == from_list [ dp_reset_n; ctrl_reset_n; latch_hidden l
                                    ; latch_clk l; latch_old_clk l
                                    ; latch_state0 l; latch_not_state0 l
                                    ; req (latch_output l); req (latch_input l); ack (latch_output l)])
      end.
      { split; intros z Hz; to_in_list_dec; simpl; simpl in Hz;    
          repeat (compare_next; auto).
        destruct l; simpl in *; find_contradiction.
        destruct l; simpl in *; find_contradiction.
      }
      rewrite HX in *; clear HX.

      combine_state_equiv_on_complex.
      { apply state_equiv_on_disjoint; auto.
        intros z Hz. unfold update. compare_next; auto.
        contradict Hz.
        apply not_in_intersection.
        left. 
        destruct l; simpl; solve_set.
      }
      standardize_state_equiv_on_set Hequiv.

      match goal with
      | [ Hequiv : state_equiv_on ?X _ _ |- _ ] =>
        assert (HX : X == space_domain (latch_stage_with_env l))
      end.
      { rewrite dom_latch_stage_with_env. clear Hequiv.
        split; intros z Hz; to_in_list_dec;
          simpl; simpl in Hz;
          repeat (compare_next; auto).
      }
      rewrite HX in Hequiv. clear HX.
      

      assert (H_val_is_bit : forall x0 : name, x0 ∈ space_domain (latch_stage_with_env l) ->
                             val_is_bit (σ' x0)).
      {
        intros y HY.
        rewrite_state_equiv; auto.
        simpl. repeat compare_next; auto.
        assert (Hstate0 : val_is_bit (σ (latch_state0 l))).
        { apply Hwf1. rewrite dom_latch_stage_with_env. solve_space_set. }
        destruct l; simpl; auto. inversion Hstate0; constructor.
      }
      constructor.

      + (* val_is_bit *) auto.
      + (* ctrl_reset_n *)
        rewrite_state_equiv; auto.
        rewrite dom_latch_stage_with_env. to_in_list_dec. auto.
      + (* dp_reset_n *)
        rewrite_state_equiv; auto.
        rewrite dom_latch_stage_with_env. to_in_list_dec. auto.
      + (* latch_hidden *)
        rewrite_state_equiv; auto.
        2:{ rewrite dom_latch_stage_with_env. to_in_list_dec. simpl. reduce_eqb; auto. }
        { simpl. reduce_eqb. auto. }
      + (* stable *) admit.
      + (* stable *) admit.
      + (* clk vs state0 *)
        rewrite dom_latch_stage_with_env in Hequiv.
        rewrite_state_equiv; [ simpl; try reduce_eqb | solve_space_set ].
        rewrite_state_equiv; [ simpl; try reduce_eqb | solve_space_set ].
        rewrite_state_equiv; [ simpl; try reduce_eqb | solve_space_set ].
        rewrite_state_equiv; [ simpl; try reduce_eqb | solve_space_set ].
        auto.

    * admit.
    * admit.
    * admit.
  Admitted.


  Lemma step_wf_state_eps : forall l σ σ',
    wf_stage_state l σ ->
    latch_stage_with_env l ⊢ σ →{None} Some σ' ->
    wf_stage_state l σ'.
  Proof.
    intros l σ σ' [Hwf1 Hwf2 Hwf3 Hwf4] Hstep.
    set (Hdisjoint := scheme_all_disjoint l).

    repeat step_inversion_1; repeat combine_state_equiv_on.
    * standardize_state_equiv_on_set Hequiv0.
        match type of Hequiv0 with
        | state_equiv_on ?X ?τ ?τ' =>
            assert (HX : X == from_list [req (latch_input l); ack (latch_output l); ack (latch_input l); 
                               req (latch_output l); latch_clk l; latch_state0 l; latch_not_state0 l; 
                               latch_hidden l; ctrl_reset_n; dp_reset_n])
        end.
        { split; intros x Hx; to_in_list_dec;
            simpl in Hx; repeat compare_next; simpl; reduce_eqb; auto.
        }
        rewrite HX in Hequiv0. clear HX.
      assert (Hold : σ' (latch_old_clk l) = σ (latch_clk l)).
      { inversion Hstep; subst.
        rewrite <- H2.
        2:{ destruct l; solve_space_set. }
        unfold update. reduce_eqb; auto.
      }
      constructor.
      + intros x Hx. rewrite dom_latch_stage_with_env in Hx.
        compare x (latch_old_clk l).
        { (* eq *) rewrite Hold.
          apply Hwf1. rewrite dom_latch_stage_with_env. solve_space_set.
        }
        { (* <> *) rewrite <- Hequiv0.
          { apply Hwf1. rewrite dom_latch_stage_with_env. auto. }
          { to_in_list_dec. simpl in Hx.
            repeat compare_next; simpl; reduce_eqb; auto.
          }
        }
      + rewrite_state_equiv; auto.
        { solve_space_set. }
      + rewrite_state_equiv; auto.
        { solve_space_set. }
      + rewrite_state_equiv; auto.
        { solve_space_set. }
      + admit.
      + admit.
      + rewrite <- Hequiv0; [ | solve_space_set].
        rewrite <- Hequiv0; [ | solve_space_set].
        rewrite <- Hequiv0; [ | solve_space_set].
        rewrite Hold.
        auto.

    * standardize_state_equiv_on_set Hequiv1.
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

End WFStage.


(*
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
*)
