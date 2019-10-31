Require Import FlowEquivalence.
Require Import List.
Import ListNotations.
Open Scope list_scope.


  Arguments odd_even_neighbors {even odd}.
  Arguments even_odd_neighbors {even odd}.

Section RiseDecoupled.

  Context (even odd : Set).
  Context `{Heven : eq_dec even} `{Hodd : eq_dec odd}.
  Variable c : circuit even odd. Print circuit.

  Inductive transitions_RD : Set :=
  | Even_fall (A : even) : transitions_RD
  | Even_rise (A : even) : transitions_RD
  | Odd_fall  (B : odd) : transitions_RD
  | Odd_rise  (B : odd) : transitions_RD
  | Even_odd_fall (A : even) (B : odd) : In (A,B) (even_odd_neighbors c) -> transitions_RD (* A- → B- *)
  | Odd_even_rise (A : even) (B : odd)  : In (A,B) (even_odd_neighbors c) -> transitions_RD (* B- → A+ *)
  | Even_odd_rise (A : odd)  (B : even) : In (A,B) (odd_even_neighbors c) -> transitions_RD (* B- → A+ *)
  | Odd_even_fall (A : odd)  (B : even) : In (A,B) (odd_even_neighbors c) -> transitions_RD (* A- → B- *)
  .

  Instance eqdecRD : eq_dec transitions_RD.
  Proof.
    split. intros t1 t2.
    destruct t1; destruct t2; try (right; inversion 1; fail).
    destruct Heven as [Heven'], Hodd as [Hodd'].
  Admitted.

  Program Fixpoint flat_map_proof {A B C : Type}
                          (ls : list (A*B))
                        : (forall (a : A) (b : B), In (a,b) ls -> list C)
                       -> list C :=
    match ls with
    | [] => fun _ => []
    | (a,b) :: ls' => fun f => f a b _ ++ flat_map_proof ls' (fun a' b' pf' => f a' b' _)
    end.

  Definition rise_decoupled 
           : marked_graph (event even odd) transitions_RD :=
  {| input_event_output := 
     let eo_f := fun (A : even) (B : odd) pf =>
                     [ (Pos (Even A), Even_fall A, Neg (Even A))
                     ; (Neg (Even A), Even_odd_fall A B pf, Neg (Odd B))
                     ; (Neg (Odd B), Odd_even_rise A B pf, Pos (Even A))
                     ; (Pos (Odd B), Odd_fall B, Neg (Odd B))
                     ; (Neg (Odd B), Odd_rise B, Neg (Odd B))
                     ]
     in
     let oe_f := fun (A : odd) (B : even) pf =>
                     [ (Pos (Odd A), Odd_fall A, Neg (Odd A))
                     ; (Neg (Odd A), Odd_even_fall A B pf, Neg (Even B))
                     ; (Neg (Even B), Even_odd_rise A B pf, Pos (Odd A))
                     ; (Pos (Even B), Even_fall B, Neg (Even B))
                     ; (Neg (Even B), Even_rise B, Pos (Even B))
                     ]
     in flat_map_proof (even_odd_neighbors c) eo_f
     ++ flat_map_proof (odd_even_neighbors c) oe_f
   |}.


(*
  Definition even_neighbors_left (c : circuit even odd) (e : even) : list odd :=
    let f := fun oe => if snd oe =? e then [fst oe] else [] in
    flat_map f (odd_even_neighbors c).
  Definition even_neighbors_right (c : circuit even odd) (e : even) : list odd :=
    let f := fun eo => if fst eo =? e then [snd eo] else [] in
    flat_map f (even_odd_neighbors c).
  Definition odd_neighbors_left (c : circuit even odd) (o : odd) : list even :=
    let f := fun eo => if snd eo =? o then [fst eo] else [] in
    flat_map f (even_odd_neighbors c).
  Definition odd_neighbors_right (c : circuit even odd) (o : odd) : list even :=
    let f := fun oe => if fst oe =? o then [snd oe] else [] in
    flat_map f (odd_even_neighbors c).
*)

  Require Import Monad.

(*
  Definition rise_decoupled 
           : marked_graph (event even odd) transitions_RD :=
  {| in_transitions := fun (E : event even odd) =>
    match E with
    | Pos (Even e) => [Even_rise e] ++ fmap (Odd_even_rise e) (even_neighbors_right e)
    | Neg (Even e) => [Even_fall e] ++ fmap (Odd_even_fall e) (even_neighbors_left e)
    | Pos (Odd o)  => [Odd_rise o]  ++ fmap (Even_odd_rise o) (odd_neighbors_right o)
    | Neg (Odd o)  => [Odd_fall o] ++ fmap (Even_odd_fall o) (odd_neighbors_left o)
    end
  ; out_transitions := fun (E : event even odd) =>
    match E with
    | Pos (Even e) => [Even_fall e]
    | Neg (Even e) => fmap (fun o => Even_odd_fall o e) (even_neighbors_right e)
    | Pos (Odd o)  => [Odd_fall o]
    | Neg (Odd o)  => [Odd_rise o] 
                   ++ fmap (fun e => Odd_even_rise e o) (odd_neighbors_left o)
                   ++ fmap (fun e => Odd_even_fall e o) (odd_neighbors_right o)
    end
  |}.
*)

  Definition rise_decoupled_init  : marking transitions_RD :=
    fun t => match t with
             | Even_fall e => 1
             | Odd_even_fall _ _ _ => 1
             | Odd_rise _  => 1
             | _ => 0
             end.



    Lemma find_ith_occurrence_empty_async :
      forall (i : nat) (e : event even odd) (lset : latch_set even odd),
             find_ith_occurrence e (ls_empty_async lset) i = None.
    Proof.
      induction i; intros e lset; auto.
    Qed. Print ls_empty_sync.
    Lemma find_ith_occurrence_empty_sync :
      forall (i : nat) (e : event even odd) (clk : CLK),
             find_ith_occurrence e (ls_empty_sync clk) i = None.
    Proof.
      induction i; intros e lset; auto.
    Qed.

Existing Instance event_eq_dec.

  Require Import Program.
  Theorem rise_decoupled_flow_equivalence :
    flow_equivalence rise_decoupled rise_decoupled_init c CLK0.
  Proof.
    unfold flow_equivalence. Print latch_sequence.
    dependent induction s; [rename l into lset | ]; intros Hconsistent l i.
    * simpl.
      induction i; simpl; auto.
    * specialize (IHs s eq_refl JMeq_refl).
      dependent destruction i; auto.
      simpl.
      unfold eqb.
      destruct (e =? transparent_event even odd l) as [e_eq_l | e_neq_l].
      + Print sync_latch_sequence. destruct 

      destruct l as [lE | lO].
      + simpl.
        

      destruct i as [ | i]; [reflexivity | ].
      simpl.



      assert (Hsync :
              find_ith_occurrence (transparentEvent even odd l) 
                                  (sync_latch_sequence even odd (ls_length even odd s) CLK0)
                                  i'
              = Some 0 
          \/ find_ith_occurrence (transparentEvent even odd l) 
                                  (sync_latch_sequence even odd (ls_length even odd s) CLK0)
                                  i'
              = Some 1)
        by admit.



Locate "_ ~= _". Print JMeq.
      simpl.
      Print projection.
      


    intros s Hconsistent l i.
Print projection.
    induction i as [ | i'].
    * simpl. reflexivity.
    * simpl. Print sync_latch_sequence. 
      destruct Hsync as [Hsync | Hsync]; rewrite Hsync; clear Hsync.
      + simpl.
        rewrite IHi'.

  Abort.


End RiseDecoupled.
Arguments rise_decoupled {even odd}.

Section RDFlowEquivalence.

  Context (even odd : Set).
  Context `{Heven : eq_dec even} `{Hodd : eq_dec odd}.

  Context (c : circuit even odd).
  
  Theorem rise_decoupled_flow_equivalence : forall c,
    flow_equivalence rise_decoupled rise_decoupled_init c all_even_events_rd all_odd_events_rd.
  Proof.
    intros c. intros s Hconsistent.
    unfold consistent_with_MG in Hconsistent.
    intros [o | e] i.
    induction i.
    * simpl. reflexivity.
    * simpl.
      set (SYNC := (repeat (ls_length evenRD oddRD s) [all_even_events_rd; all_odd_events_rd])).
      destruct l as [o | e].
      + simpl. 
        assert (Hsync : (find_ith_occurrence (Pos (Odd o)) SYNC i = Some (2*i))) (* or opposite? *)
         by admit.
        rewrite Hsync.
        unfold all_even_events_rd. unfold all_odd_events_rd.
        unfold sync_latch_sequence.
        destruct (find_ith_occurrence (Pos (Odd o)) (next_events s) i)
          as [t | ] eqn:Ht.
        ++ admit.
        ++ rewrite IHi.
           admit (*?*).
  Abort.  


End RDFlowEquivalence.
