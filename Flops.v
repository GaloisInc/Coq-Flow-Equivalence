Require Import Base.
Require Import Monad.
Import Monad.Instances.
Require Import FlowEquivalence.
Import FE_Tactics.

Require Import List.
Import ListNotations.
Open Scope list_scope.


Set Implicit Arguments.

Section Flops.


  (* Trying to avoid master/slave terminology *)
  Inductive master_latch (flop : Set) : Set :=
  | Master : flop -> master_latch flop.
  Inductive clone_latch (flop : Set) : Set :=
  | Clone : flop -> clone_latch flop.
  Definition from_master {flop} (f : master_latch flop) : flop :=
    match f with
    | Master f' => f'
    end.
  Definition from_clone {flop} (f : clone_latch flop) : flop :=
    match f with
    | Clone f' => f'
    end.


  Record FF_circuit (flop : Set) := 
    { ff_neighbors : list (flop * flop)
    ; ff_next_state : forall (f : flop),
      state {fpred : flop & In (fpred,f) ff_neighbors} -> value
    }.
  Definition restrict_state {flop : Set} {P : flop -> Prop}
                       (s : state flop) : state {f : flop & P f} :=
    fun f => s (projT1 f).

  Section FF_to_latch.

    Variable flop : Set.
    Variable c : FF_circuit flop.
    Variable flop_bank : list flop.

    Hypothesis all_flop_bank : forall f, In f flop_bank.    

    Let master_clone_neighbor (f : flop) := (Master f,Clone f).
    Let clone_master_neighbor (fs : flop * flop) := (Clone (fst fs), Master (snd fs)).

    Let master_clone_neighbors := fmap master_clone_neighbor flop_bank.
    Let clone_master_neighbors := fmap clone_master_neighbor (ff_neighbors c).


    Program Let convert_state f : 
        state {fpred : clone_latch flop & In (fpred,f) clone_master_neighbors } -> 
        state {fpred : flop & In (fpred, from_master f) (ff_neighbors c)} :=
      fun st fpred' => st (existT _ (Clone (projT1 fpred')) _).
    Next Obligation.
      simpl.
      unfold clone_master_neighbors.
      destruct f as [f].
      replace (Clone fpred', Master f) with (clone_master_neighbor (fpred',f)).
      2:{ unfold clone_master_neighbor. simpl. reflexivity. }
      apply in_map.
      auto.
    Defined.

    Let next_state_master (f : master_latch flop) 
             (st : state { f0 : clone_latch flop & In (f0,f) clone_master_neighbors })
            : value :=
      ff_next_state c (from_master f) (convert_state f st).

    Program Let next_state_clone (f : clone_latch flop)
            (st : state {f0 : master_latch flop & In (f0,f) master_clone_neighbors })
            : value :=
      st (existT _ (Master (from_clone f)) _).
    Next Obligation.
      unfold master_clone_neighbors.
      destruct f.
      simpl.
      replace (Master f,Clone f) with (master_clone_neighbor f)
        by reflexivity.
      apply in_map.
      auto.
    Defined.

      

    Definition FF_to_latch_circuit : circuit (master_latch flop) (clone_latch flop) :=
      {| even_odd_neighbors := master_clone_neighbors
      ;  odd_even_neighbors := clone_master_neighbors
      ;  next_state_e := next_state_master
      ;  next_state_o := next_state_clone
      |}.
  End FF_to_latch.


End Flops.
