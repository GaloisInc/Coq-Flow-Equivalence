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
  Lemma latch_stage_with_env_output : forall l,
    space_output (latch_stage_with_env l) == space_input (latch_stage l) ∪ space_output (latch_stage l).
  Proof.
    intros l'.
    split.
    { intros x Hx. simpl in Hx. decompose_set_structure; solve_set. }
    { intros x Hx. simpl in Hx. decompose_set_structure; try solve_set;
      destruct l'; simpl in *; find_contradiction.
    }
  Qed.
  Lemma latch_stage_with_env_internal : forall l,
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
    (* monoid *)
    { unfold_StateSpace (latch_stage l').
      split; intros x Hx; simpl in *; decompose_set_structure; try solve_set;
        destruct l'; simpl in *; find_contradiction.
    }
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
    | [ |- well_formed (delay_space _ _ _) ] => apply delay_space_wf; typeclasses eauto
    | [ |- in_dec _ ] => typeclasses eauto
    | [ |- _ ⊥ _ ] => constructor; intros x Hx; simpl in *; decompose_set_structure; fail
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
    intros l. unfold_StateSpace (latch_left_ack_component l).
    solve_wf.
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
        | unfold space_domain; simpl; solve_set ]
    end

  (* Hide *)
  | hide ?x0 ?S0 ⊢ _ →{Some _} _ => apply hide_inversion in Hstep
  | hide ?x0 ?S0 ⊢ _ →{None} _ => apply hide_inversion_None in Hstep;
              let v := fresh "v" in
              destruct Hstep as [Hstep | [v Hstep]]

  (* DelaySpace *)
  | delay_space ?S0 ?sensitivities ?guard ⊢ _ →{_} _ =>
    let Hequiv := fresh "Hequiv" in
    let Hguard := fresh "Hguard" in
    apply delay_space_inversion in Hstep;
    [ destruct Hstep as [Hstep [Hequiv Hguard]]

    (*
      (* clean up Hguard so it doesn't have any occurrences of (_ =? _) *)
      repeat match type of Hguard with
      | event_in ?X ?e -> _ => 
        assert (Hin : event_in X e);
        [ constructor; solve_space_set; auto; fail
        | specialize (Hguard Hin); clear Hin ]
      | (?x =? ?y) = true =>
        let Hguard' := fresh "Hguard" in
        assert (Hguard' : x = y);
        [ compare x y | ]
      | event_in ?X ?e -> (?x =? ?y) = true =>
        let Hguard' := fresh "Hguard" in
        assert (Hguard' : event_in X e -> x = y);
        [ let Hin := fresh "Hin" in
          intro Hin;
          apply Hguard in Hin;
          compare x y
        | ]
      end; clear Hguard
    *)

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
  | [ Hstep : delay_space _ _ _ ⊢ _ →{_} _ |- _ ] =>
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
(*    intros l.
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
  Qed.
*)
  Admitted (* true but slow *).


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

  Lemma step_wf_state_lemma : forall l σ e σ',
    wf_stage_state l σ ->
    latch_stage_with_env l ⊢ σ →{Some e} Some σ' ->
    wf_stage_state l σ'.
  Proof.
    intros l σ [x v] σ' [Hwf1 Hwf2 Hwf3 Hwf4] Hstep.
    assert (Hx : x ∈ space_input (latch_stage_with_env l) ∪ space_output (latch_stage_with_env l)).
    { eapply wf_space; eauto. }
    rewrite latch_stage_with_env_input, latch_stage_with_env_output in Hx.
    rewrite latch_stage_input, latch_stage_output in Hx.
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
      + admit (* need to know more about stability? *).

    * (* r_ack *)
      repeat (step_inversion_1; try combine_state_equiv_on).

      standardize_state_equiv_on_set Hequiv1.
      standardize_state_equiv_on_set Hequiv2.

      match type of Hequiv2 with
      | state_equiv_on ?X _ _ =>
        assert (HX : X == from_list [dp_reset_n; ctrl_reset_n; latch_hidden l
                                    ; latch_clk l; latch_old_clk l
                                    ; latch_state0 l; latch_not_state0 l
                                    ; req (latch_output l); req (latch_input l); ack (latch_input l)])
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
        apply Hwf1. rewrite dom_latch_stage_with_env. to_in_list_dec. simpl. reduce_eqb. auto.
      }
      constructor.

      + (* val_is_bit *) admit.
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

    * admit.
    * admit.
    * admit.
  Admitted.
(*


        

        match



    constructor.
    * (* val_is_bit *)
      intros y Hy.
      decompose_set_structure.
      + (* x = l_req *) admit (* works but slow 
        repeat step_inversion_1.
      
(*
      repeat match goal with
      | [ H : context[ hide (latch_not_state0 ?l) ?S ] |- _ ] => replace (hide (latch_not_state0 l) S)
                                                           with (latch_flop_component l)
                                                           in H
                                                           by reflexivity
      | [ H : context[ delay_space ?S0 ?l0 ?guard ] |- _ ] =>
        replace (delay_space S0 l0 guard)
        with (latch_left_ack_component l)
        in H
        by reflexivity

      end.
*)

        repeat combine_state_equiv_on.
        combine_state_equiv_on_complex.
        { apply state_equiv_on_disjoint; auto.
          intros z Hz. unfold space_domain in Hz. simpl in Hz.
          unfold update. compare_next; auto.
          contradict Hz.
          apply not_in_intersection.
          left.
          destruct l; simpl; solve_set.
        }
        2:{ rewrite dom_latch_stage_with_env in Hy.
            unfold space_domain. simpl.
            to_in_list_dec. simpl in Hy. repeat (compare_next; [solve_set | ]).
            compare_next. destruct l; solve_set. 
        }

       { match goal with
         | [ |- context[ y ∈? ?Y ] ] => destruct (y ∈? Y); try solve_val_is_bit
         end.
         compare_next; solve_val_is_bit.
       } *).

     + (* x = r_ack *) admit (* works but slow 
        repeat step_inversion_1.
        repeat combine_state_equiv_on.
        combine_state_equiv_on_complex.
        { apply state_equiv_on_disjoint; auto.
          intros z Hz. unfold space_domain in Hz. simpl in Hz.
          unfold update. compare_next; auto.
          contradict Hz.
          apply not_in_intersection.
          right.
          destruct l; simpl; solve_set.
        }
        2:{ rewrite dom_latch_stage_with_env in Hy.
            to_in_list_dec. simpl in Hy.
            unfold space_domain. simpl.
            repeat (compare_next; [solve_set | ]).
            compare_next. destruct l; solve_set. 
        }
       { match goal with
         | [ |- context[ y ∈? ?Y ] ] => destruct (y ∈? Y); try solve_val_is_bit
         end.
         compare_next; try solve_val_is_bit.
         apply Hwf1. rewrite dom_latch_stage_with_env. solve_set.
       } *).

     + (* x = l_ack *) admit (* good but slow 
        repeat (step_inversion_1; try combine_state_equiv_on).

        (* simplify Hguard *)
        simpl in Hguard.
        assert (Hguard' : σ (latch_and_nat l "clk") = Bit0).
        { compare_next; auto.
          absurd (false = true); [inversion 1 | ].
          apply Hguard.
          constructor.
          solve_set.
        }
        clear Hguard.

        combine_state_equiv_on_complex.
        { apply state_equiv_on_disjoint; auto.
          intros z Hz. unfold space_domain in Hz. simpl in Hz.
          unfold update. compare_next; auto.
          contradict Hz.
          apply not_in_intersection.
          left.
          destruct l; simpl; solve_set.
        }
        2:{ rewrite dom_latch_stage_with_env in Hy.
            to_in_list_dec. simpl in Hy.
            unfold space_domain. simpl.

            repeat (compare_next; [try solve_set | ]).
            compare_next. destruct l; solve_set.
        }
        { match goal with
          | [ |- context[ y ∈? ?Y ] ] => destruct (y ∈? Y); try solve_val_is_bit
          end.
          compare_next; try solve_val_is_bit.
       } *).

     + (* x = r_req *) admit (* good but slow 
        repeat (step_inversion_1; try combine_state_equiv_on).

        combine_state_equiv_on_complex.
        { apply state_equiv_on_disjoint; auto.
          intros z Hz. unfold space_domain in Hz. simpl in Hz.
          unfold update. compare_next; auto.
          contradict Hz.
          apply not_in_intersection.
          left.
          destruct l; simpl; solve_set.
        }
        2:{ rewrite dom_latch_stage_with_env in Hy.
            to_in_list_dec. simpl in Hy.
            unfold space_domain. simpl.

            repeat (compare_next; [try solve_set | ]).
            compare_next. destruct l; solve_set.
        }
        { match goal with
          | [ |- context[ y ∈? ?Y ] ] => destruct (y ∈? Y); try solve_val_is_bit
          end.
          compare_next; try solve_val_is_bit.
       } *).


     + (* x = clk *) admit (* WIP
        do 5 step_inversion_1. combine_state_equiv_on.
        do 5 step_inversion_1. repeat combine_state_equiv_on.
        do 3 step_inversion_1. repeat combine_state_equiv_on.
        

        (* simplify Hguard *)
        simpl in Hguard. clear Hguard.

        repeat (step_inversion_1; try combine_state_equiv_on).

        combine_state_equiv_on_complex.
        { apply state_equiv_on_disjoint; auto.
          intros z Hz. unfold space_domain in Hz. simpl in Hz.
          unfold update. compare_next; auto.
          (* Hstep2 inversion *) admit.
        }
        2:{ rewrite dom_latch_stage_with_env in Hy.
            to_in_list_dec. simpl in Hy. admit (*?*).
        }
        { match goal with
          | [ |- context[ y ∈? ?Y ] ] => destruct (y ∈? Y); try solve_val_is_bit
          end.
          compare_next; try solve_val_is_bit.
          destruct l; admit (* lemma *).
       } *).

  * (* wf_handshake *)

        repeat step_inversion_1.
        repeat combine_state_equiv_on.




        rewrite_state_equiv_branch y.
        { compare_next; try solve_val_is_bit. }
        rewrite_state_equiv_branch y.
        { solve_val_is_bit. }
        { contradict Hy.
          intros Hy. Search (_ ∉ _ -> _ ∉ _ -> _ ∉ (_ ∪ _)).

Lemma not_in_union : forall {X} (x : X) A B,
    x ∉ A -> x ∉ B -> x ∉ (A ∪ B).
Admitted.

          apply (not_in_union _ _ _ Hy0) in Hy1; clear Hy0.
          contradict Hy1.
          unfold space_domain in *. simpl in *.
          decompose_set_structure; try solve_set.
        }


 unfold space_domain in Hy. simpl in Hy.
          unfold space_domain in Hy1. simpl in Hy1.
          decompose_set_structure
        


          
        rewrite_state_equiv.

        match goal with
        | [ y : name
          , Hequiv : state_equiv_on ?X (Some ?σ) (Some ?σ') |- context[ ?σ' y ] ] =>
          let Hy := fresh "Hy" in
          destruct (y ∈? X) as [Hy | Hy];
            [ rewrite_state_equiv
            | clear Hequiv]
        end.

        compare_next; try solve_val_is_bit. 
        

Search val_is_bit neg_value.
    let Hbit := fresh "Hbit" in
    assert (Hbit : val_is_bit (σ (latch_and_nat l "l_ack"))). apply Hwf1. 

unfold_StateSpace (latch_stage_with_env l).
solve_space_set.

 unfold space_domain. simpl. solve_set. by solve_val_is_bit.
    inversion Hbit; subst;
    auto with click
        
About func_space_inversion.

        compare_next.
        rewrite_state_equiv.

          
        rewrite_state_equiv_on.




  decompose_set_structure (* from Hx *).

  *
  (* TODO: make all this happen automatically via decide_events_in tactic *)





  repeat step_inversion_1.



  constructor.
  + intros y Hy.

HHHHHHHHHHHHHHHHHHHHHHHHHHHHH
  
  

set_to_list HS ((from_list [ack (latch_input l)]
               ∪ singleton (req (latch_input l)))
              ∪ (from_list
                   [latch_state0 l; req (latch_input l); 
                   ack (latch_output l); ctrl_reset_n (odd:=odd)]
                 ∪ singleton (latch_clk l))).

  Ltac state_equiv_on_to_list :=
  match goal with
  | [ Hequiv : state_equiv_on (space_domain ?S) _ _ |- _ ] =>
    unfold_StateSpace S in Hequiv;
    match type of Hequiv with
    | state_equiv_on (space_domain ?S0) _ _ =>
      let S0' := reflect_ISpace S0 in
      replace (space_domain S0)
        with (space_domain (interp_ISpace S0'))
        in Hequiv
        by reflexivity;
      rewrite space_domain_ISpace in Hequiv;
      let l0 := eval simpl in (ISpace_dom S0') in
      replace (from_list (ISpace_dom S0'))
        with  (from_list l0)
        in    Hequiv
        by reflexivity

    end

  | [ Hequiv : state_equiv_on ?X _ _ |- _ ] =>
    let HX := fresh "HX" in
    set_to_list HX X;
    rewrite HX in Hequiv;
    clear HX

  end.


  state_equiv_on_to_list.
  state_equiv_on_to_list.
  match goal with
  | [ Hequiv : state_equiv_on (from_list ?l) (Some _) (Some ?σ')
    |- context[ ?σ' ?y ] ] =>
    let Hy := fresh "Hy" in
    destruct (y ∈? from_list l) as [Hy | Hy];
    [ rewrite <- Hequiv;
      try unfold update;
      repeat compare_next; auto;
      try solve_val_is_bit
    | clear Hequiv ]
  end.

  assert (Hy' : y ∈ space_domain (latch_stage_with_env l) ∖
              from_list [ack (latch_input l); req (latch_input l); 
            latch_state0 l; req (latch_input l); ack (latch_output l);
            ctrl_reset_n (odd:=odd); latch_clk l]).
  { solve_set. }
  clear Hy0.

als;dkg;eioghe;ofijeiojf;oeh

  (* TODO: trying to figure out a way to implement setmins better *)
  (* get assumptions in conclusion *) Print all_disjoint.
  repeat match goal with
  | [ H : all_disjoint (?x :: _) |- _ ] =>
    inversion H; subst; clear H
  end.
  to_in_list_dec.
  repeat match goal with
  | [ Hdec : in_list_dec ?x ?l = _ |- _ ] => simpl in Hdec
  end.
  repeat compare_next.
Search all_disjoint.
    dependent destruction Hdisjoint.
  inversion Hdisjoint as [ | Hdisjoint'].
  simpl in Hdisjoint.

  unfold_StateSpace (latch_stage_with_env l) in Hy';
  match type of Hy' with
  | ?y ∈ ?S =>
    let S0 := reflect_to_SetStructure S in
    let l0' := eval simpl in (SetStructure_to_list S0) in
    assert (HS' : S == from_list l0');
    [ transitivity (interpret_SetStructure S0);
      [ reflexivity | rewrite SetStructure_to_list_correct; reflexivity]
    | rewrite HS' in Hy'; clear HS'
    ]
  end.
  unfold list_setminus in Hy'.
  simpl in Hy'.
  to_in_list_dec.

Print naming_scheme.

  Lemma 
  Ltac compare_concrete H x y :=
    match constr:((x, y)) with
    | (?z, ?z) => rewrite (eqb_eq _ z) in H; auto
    | (?z1, ?z2) => rewrite (eqb_neq _ z1 z2) in H;
      [
      | intro; find_contradiction;
      (* in case there is a latch_to_token_flag in there *)
        try match z1 with
        | match latch_to_token_flag ?l0 with
          | Token => _
          | NonToken => _
          end =>
          destruct l0; simpl in *;
          find_contradiction;
          fail
        end;
        try match z2 with
        | match latch_to_token_flag ?l0 with
          | Token => _
          | NonToken => _
          end =>
          destruct l0; simpl in *;
          find_contradiction;
          fail
        end;
        fail
      ]
    end.

  compare_concrete Hy' (req (latch_input l)) (ack (latch_input l)).
  
  do 20 match goal with
  | [ H : context[ ?z' =? ?z ] |- _ ] => compare_concrete H z' z; simpl in H
  end.
  do 10 match goal with
  | [ H : context[ ?z' =? ?z ] |- _ ] => compare_concrete H z' z; simpl in H
  end.
  do 10 match goal with
  | [ H : context[ ?z' =? ?z ] |- _ ] => compare_concrete H z' z; simpl in H
  end.
  do 10 match goal with
  | [ H : context[ ?z' =? ?z ] |- _ ] => compare_concrete H z' z; simpl in H
  end.
  do 10 match goal with
  | [ H : context[ ?z' =? ?z ] |- _ ] => compare_concrete H z' z; simpl in H
  end.
  do 2 match goal with
  | [ H : context[ ?z' =? ?z ] |- _ ] => compare_concrete H z' z; simpl in H
  end.



    rewrite space_domain_ISpace in Hequiv1.
    simpl in Hequiv1.
    reflexivity.
  
  transitivity (space_domain (interp_ISpace 

  match goal with
  | [ H : ?y ∈ ?Y
    ; state_equiv_on ?X1 (Some ?σ) (Some ?σ')
    ; state_equiv_on ?X2 (Some ?σ) (Some ?σ')
    |- context[ ?σ' ?y ] ] =>
    assert (
  end.
(*    rewrite Hdom in Hy.*)
    destruct (y ∈? (from_list
                [latch_state0 l; req (latch_input l); 
                ack (latch_output l); ctrl_reset_n (odd:=odd); latch_clk l]))
      as [Hy' | Hy'].
    { rewrite <- Hequiv; auto.
      2:{ to_in_list_dec; simpl in Hy'.
          repeat compare_next; solve_set.
      }
      unfold update.
      compare_next; auto.
      solve_val_is_bit.
    }
    destruct (y ∈? (from_list [ack (latch_input l); req (latch_input l)]))
      as [Hy'' | Hy''].
    { rewrite <- Hequiv0; auto.
      2:{ to_in_list_dec; simpl in Hy''.
          repeat compare_next; solve_set. }
      unfold update.
      compare_next; auto.
      solve_val_is_bit.
    }
    repeat to_in_list_dec.
    simpl in Hy', Hy''.
    repeat compare_next.

   space_domain_to_list Hdom (latch_stage_with_env l).
   rewrite Hdom in Hy. clear Hdom.
   to_in_list_dec.
    simpl in Hy.
    repeat compare_next.
  
rewrite_state_equiv_on. rewrite <- Hequiv0.
      apply Hwf1.



 unfold space_domain in *. simpl in *.
    decompose_set_structure.
  

    2:{ contradict He1. constructor. unfold space_domain; simpl; solve_set.
    2:{
    inversion He2 as [? He']; subst; clear He2;
    contradict He'; unfold space_domain; simpl; solve_set; fail.
    find_event_contradiction.

    contradict He2. inversion 1; subst. contradict pf. unfold space_domain. simpl. solve_set.
  repeat match goal with
  | [ He : event_in _ _ None |- _ ] => inversion He; fail
  | [ He : event_in _ _ (Some (Event x v)) |- _ ] => 
    let He' := fresh "He" in
    inversion He as [? He']; subst; clear He;
    try unfold space_domain in He'; simpl in He'
  end.


  | [ H : _ ∈ space_domain _ |- _ ] => unfold space_domain in H; simpl in H
  | [ H : _ ∉ space_domain _ |- _ ] => unfold space_domain in H; simpl in H
  end.

  

    destruct (decide_event_in (Some (Event x v)) (space_domain (left_env_component l ∥ latch_stage l))) as [He1 | He1];
    destruct (decide_event_in (Some (Event x v)) (space_domain (right_env_component l))) as [He2 | He2].

    inversion Hstep.


  replace (latch_stage_with_env l) with (S1 ∥ S2); unfold S1, S2; clear S1 S2. 2:{ reflexivity. } clear S1; clear S2.
  ereplace (latch_stage_with_env l) with _.

  match goal with
  | [ H : ?S ⊢ _ →{?e} Some _ |- _ ] =>
    replace S with (_ ∥ _) in H
  end.

  match goal with
  (* union *)
  | [ H : ?S ⊢ _ →{?e} Some _ |- _ ] =>

    destruct (decide_event_in e (space_domain S)) as [He | He]
  end.


(*
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

    * destruct (y ∈? space_internal (latch_stage_with_env l)) as [Hinternal | Hinternal].
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
        inversion Hwf2 as [Hwf2' | Hwf2'].
        + right. repeat rewrite_step_inversion.
          step_inversion_eq. subst.
          rewrite Hwf2'.
          rewrite Hstate0'.
          destruct l; simpl; auto.

          rewrite val_is_bit_neg_neg; auto. solve_val_is_bit.

        + left. repeat rewrite_step_inversion.
          step_inversion_eq. subst.
          rewrite Hwf2'.
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

    * (* wf_handshake *)
      assert (Hstate0 : σ (req (latch_output l)) = neg_value (σ (latch_state0 l))).
      { replace v with (σ (latch_state0 l)) in * by (step_inversion_eq; auto).
        step_inversion_unstable.
        erewrite val_is_bit_neq; eauto; solve_val_is_bit.
      }

  Admitted.

Ltac solve_wf_1 := match goal with
| [ |- well_formed (latch_stage_with_env _) ] => apply latch_stage_well_formed
| [ |- well_formed _ ] => apply func_wf; solve_set

| [ |- well_formed _ ] => apply wf_union;
                [ try unfold space_domain; simpl; solve_set
                | try unfold space_domain; simpl; solve_set
                | | ]
| [ |- well_formed _ ] => apply hide_wf
| [ |- well_formed _ ] => apply delay_space_wf
| [ |- well_formed _ ] => apply flop_wf; 
    try match goal with
    [ |- context[latch_to_token_flag ?l] ] => destruct l
    end;
    repeat constructor; solve_set
end.
Ltac solve_wf := repeat solve_wf_1.

Ltac rewrite_wf_scoped :=
match goal with
| [ Hstep : ?S ⊢ ?σ →{ ?e } Some ?σ' |- context[?σ' ?x] ] =>
    let Hwf := fresh "Hwf" in
    assert (Hwf : well_formed S) by solve_wf;
    let Hneq := fresh "Hneq" in
    assert (Hneq : forall v, e <> Some (Event x v))
      by (intro; inversion 1; subst; find_contradiction);
    let Hinternal := fresh "Hinternal" in
    assert (Hinternal : x ∈ space_input S ∪ space_output S)
      by (simpl; unfold space_domain in *;
             try (decompose_set_structure; solve_set); fail);
    rewrite (wf_scoped _ _ Hwf _ _ _ Hstep _ Hneq Hinternal)
end.


Ltac step_inversion_None :=
             try match goal with
             | [ Hstep : _ ⊢ _ →{None} Some _ |- _ ] => step_inversion_1
             end;
             try match goal with
             | [ Hstep : _ ⊢ _ →{Some (Event ?y ?v) } Some ?σ' |- context[ ?σ' ?x ] ] =>
               compare x y;
               repeat step_inversion_1

(*
             | [ |- context[update] ] => unfold update; compare_next; try solve_val_is_bit
             | [ Hstep : _ ⊢ _ →{Some (Event ?y _)} Some ?σ' |- context[?σ' ?x] ] =>
               repeat step_inversion_1;
               compare x y;
               [ match goal with
                 | [ Hstep' : ?S ⊢ _ →{_} _ |- _ ] =>
                   let Hwf := fresh "Hwf" in
                   assert (Hwf : well_formed S) by solve_wf;
                   rewrite (wf_update _ _ Hwf _ _ _ _ Hstep');
                   step_inversion_eq; subst; try constructor; solve_val_is_bit
                 end
               | rewrite_wf_scoped; solve_val_is_bit
               ]*)
             end.

Ltac rewrite_state_equiv :=
  match goal with
  | [ H : state_equiv_on _ (Some ?σ') (Some _) |- context[?σ'] ] =>
      rewrite H; [ | solve_set]
  end.

Lemma latch_stage_with_env_internal' : forall l,
       space_internal (latch_stage_with_env l)
    == from_list [latch_state0 l; latch_not_state0 l
                 ; latch_old_clk l; latch_hidden l
                 ; @ctrl_reset_n even odd _; @dp_reset_n even odd _].
Proof.
    intros. simpl. split; intros x Hx; decompose_set_structure; solve_set.
Qed.
*)*)

  Lemma step_wf_state_eps : forall l σ σ',
    wf_stage_state l σ ->
    latch_stage_with_env l ⊢ σ →{None} Some σ' ->
    wf_stage_state l σ'.
  Proof.
    intros l σ σ' [Hwf1 Hwf2 Hwf3 Hwf4] Hstep.
    set (Hdisjoint := scheme_all_disjoint l).
(*
    repeat step_inversion_1.
    constructor.
    { intros x Hdom. rewrite dom_latch_stage_with_env in Hdom.

      do 3 step_inversion_1.
      2:{ compare x (latch_state0 l).
          { repeat step_inversion_1. 
            replace (σ' (latch_state0 l)) with x0.
            2:{ apply wf_update in Hstep2; auto.
                apply flop_wf. destruct l; repeat constructor; try solve_set.
              }
            apply flop_output_is_bit in Hstep2; auto.
            { destruct l; repeat constructor; solve_set. }
            solve_val_is_bit.
         }
         { repeat step_inversion_1. Print well_formed.
           
           apply func_space_output_inversion in Hstep1.
         

solve_val_is_bit.
apply func_space_output_inversion in Hstep2.

do 11 (try step_inversion_1).
        

repeat step_inversion_1.
        
      unfold
      

      step_inversion_None.

      rewrite H2. 2:{ solve_set.
      rewrite_state_equiv.

      destruct (x ∈? space_internal (latch_stage_with_env l)).
      2:{ rewrite_wf_scoped. solve_val_is_bit. }
      1:{ rewrite latch_stage_with_env_internal' in *. 
          decompose_set_structure.
          step_inversion_None.
          rewrite H2. 2:{ solve_set. }
          unfold update. compare_next.

step_inversion_1. 2:{ step_inversion_1. }
          step_inversion_1. 1:{ step_inversion_1. }
          step_inversion_1. 2:{ repeat step_inversion_1. 
            compare x (latch_state0 l).
            2:{

  erewrite (wf_scoped _ _ _ _ _ _ Hstep).
    3:{ simpl. solve_set.

match goal with
| [ Hstep : ?S ⊢ ?σ →{ ?e } Some ?σ' |- context[?σ' ?x] ] =>
    match S with
    | context[x] => 
    erewrite (wf_scoped _ _ _ _ _ _ Hstep)
    end
end.

    let Hwf := fresh "Hwf" in
    assert (Hwf : well_formed S) by solve_wf;
    let Hneq := fresh "Hneq" in
    assert (Hneq : forall v, e <> Some (Event x v))
      by (intro; inversion 1; subst; find_contradiction);
    let Hinternal := fresh "Hinternal" in
    assert (Hinternal : x ∈ space_input S ∪ space_output S) end.
simpl. solve_set.
      by (simpl; unfold space_domain in *;
             try (decompose_set_structure; solve_set); fail);
    rewrite (wf_scoped _ _ Hwf _ _ _ Hstep _ Hneq Hinternal)


rewrite_wf_scoped.

apply union_inversion_lr in Hstep.
          (* the left;right is that we should only succeedd here if x ∈ output(S1) *)
      [ | unfold space_domain; simpl; solve_set; fail]
  
step_inversion_1. step_inversion_neq.

step_inversion_None.
repeat step_inversion_1. step_inversion_None.
            ++ repeat step_inversion_1.
               assert (all_disjoint
                       [match latch_to_token_flag l with
                        | Token => dp_reset_n (odd:=odd)
                        | NonToken => latch_hidden l
                        end;
                        match latch_to_token_flag l with
                        | Token => latch_hidden l
                        | NonToken => dp_reset_n (odd:=odd)
                        end;
                        latch_clk l; latch_old_clk l; latch_not_state0 l; latch_state0 l]).
               { repeat constructor; destruct l; simpl; solve_set. }

               compare x (latch_state0 l).
               { erewrite wf_update; [ | | eauto]; [ | solve_wf].
                 eapply flop_output_is_bit; [ | | eauto]; [ auto | solve_val_is_bit].
               }
               compare x (latch_old_clk l).
               { apply flop_old_clk in Hstep; auto; try solve_val_is_bit.
                 eapply flop_output_is_bit; [ | | eauto]; [auto | solve_val_is_bit].
               }
               { rewrite_wf_scoped. solve_val_is_bit. }
          }

    + assert (Hequiv : σ' (req (latch_input l)) = σ' (ack (latch_input l))
                    \/ σ' (req (latch_input l)) = neg_value (σ' (ack (latch_input l))));
      [ | destruct Hequiv; [left | right]; auto].
      step_inversion_None;
        try (repeat step_inversion_1; repeat rewrite_wf_scoped;
             inversion Hwf2; auto; fail).
      ++ repeat compare_next. inversion Hwf2; auto.
    + assert (Hequiv : σ' (req (latch_output l)) = σ' (ack (latch_output l))
                    \/ σ' (req (latch_output l)) = neg_value (σ' (ack (latch_output l))));
      [ | destruct Hequiv; [left | right]; auto].
      step_inversion_None;
        try (repeat step_inversion_1; repeat rewrite_wf_scoped;
             inversion Hwf3; auto; fail).
      ++ repeat compare_next. inversion Hwf3; auto.


    + step_inversion_None; repeat step_inversion_1. 
      { erewrite wf_update; [ | | eauto ]; [ | solve_wf].
        step_inversion_eq; subst; auto.
      }
      { rewrite_wf_scoped; auto. }


    + admit.
    + admit.
*)
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
