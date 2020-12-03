Require Import Base.
Require Import Circuit.
Require Import StateSpace.
Require Import Click.Definitions.
Require Import Monad.
Require Import Coq.Program.Equality.


Module WFStage (Export ClickModule : ClickType).
  Export click.

  Module Desync := Desync(ClickModule).
  Import Desync.

  Hint Constructors val_is_bit : click.


  (***************************************************************************
   * Show that latch stages are well-formed state spaces
  ****************************************************************************)

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



  (***************************************************************************
   * Identify invariants that hold of all states reachable by a Click stage
   * from σR
   *
  ****************************************************************************)


  Definition if_token (l : latch even odd) (v : value) :=
    match latch_to_token_flag l with
    | NonToken => neg_value v
    | Token => v
    end.

  Record wf_stage_state (l : latch even odd) (σ : state name) : Prop :=
    { wf_all_bits : forall x, x ∈ space_domain (latch_stage_with_env l) -> val_is_bit (σ x)
    ; wf_ctrl_reset_n : σ ctrl_reset_n = Bit1
    ; wf_dp_reset_n : σ dp_reset_n = Bit1
    ; wf_hidden : σ (latch_hidden l) = Bit1

    ; wf_clk_stable   : σ (latch_state0 l) = σ (latch_not_state0 l) ->
                        σ (latch_clk l) = Bit1 ->
                        σ (latch_old_clk l) = Bit1
    ; wf_clk_unstable :
      latch_clk_function l σ = Bit1 ->
      σ (latch_clk l) = Bit0 ->
      σ (latch_state0 l) = neg_value (σ (latch_not_state0 l))
    ; left_env_component_unstable :
      σ (req (latch_input l)) = σ (ack (latch_input l)) ->
      σ (latch_state0 l) = neg_value (σ (latch_not_state0 l))

    ; left_component_stable :
      σ (req (latch_input l)) = if_token l (σ (latch_state0 l)) ->
      σ (latch_state0 l) = neg_value (σ (latch_not_state0 l))

    ; wf_clk_fn_stable :
      σ (latch_clk l) <> σ (latch_old_clk l) ->
      latch_clk_function l σ = σ (latch_clk l)
    }.

  Record wf_stage_state_stable  (l : latch even odd) (σ : state name) : Prop :=
    { wf_left_ack_flop_stable  : ~ stable (latch_left_ack_component l) σ ->
                                 stable (latch_flop_component l) σ
    ; wf_left_ack_env_stable  : ~ stable (latch_left_ack_component l) σ ->
                                stable (left_env_component l) σ

    ; wf_right_req_flop_stable : ~ stable (latch_right_req_component l) σ ->
                                 stable (latch_flop_component l) σ
    ; wf_right_req_env_stable  : ~ stable (latch_right_req_component l) σ ->
                                stable (right_env_component l) σ

(*
    ; wf_clk_component_unstable : 
                latch_clk_function l σ = Bit1 ->
                σ (latch_clk l) = Bit0 ->
                stable (left_env_component l) σ /\ stable (right_env_component l) σ
             /\ stable (latch_left_ack_component l) σ /\ stable (latch_right_req_component l) σ
             /\ stable (latch_flop_component l) σ
*)
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

    }.

  Inductive wf_handshake (h : handshake) (σ : state name) : Prop :=
  | handshake_in_sync : σ (req h) = σ (ack h) -> wf_handshake h σ
  | handshake_out_of_sync : σ (req h) = neg_value (σ (ack h)) -> wf_handshake h σ.

  Lemma val_is_bit_wf_handshake : forall σ h,
    val_is_bit (σ (req h)) ->
    val_is_bit (σ (ack h)) ->
    wf_handshake h σ.
  Proof.
    intros σ h Hreq Hack.
    inversion Hreq as [Hreq' | Hreq']; inversion Hack as [Hack' | Hack'].
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


  (***************************************************************************
   * Click tactics
  ****************************************************************************)

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

  | [ |- val_is_bit _ ] => constructor; fail

  | [ H : wf_stage_state ?l ?σ |- val_is_bit (?σ ?x) ] =>
    apply (wf_all_bits _ _ H);
    rewrite dom_latch_stage_with_env;
    solve_space_set

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


  | [ |- val_is_bit _ ] =>
    rewrite_step_inversion
  end; fail.


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

(** Quickly decide whether the event e occurs in the domain of a state space S *)
  Ltac decide_event_in_domain e S :=
  match e with
  | None => assert (~ (@event_in name value (space_domain S) None))
              by inversion 1
  | Some (Event ?x ?v) =>
      let Hdom  := fresh "Hdom" in
      let Hdec0 := fresh "Hdec0" in
      space_domain_to_list Hdom S;
      match type of Hdom with
      | (space_domain ?S == from_list ?l) =>
        decide_in_list_dec Hdec0 x l;
        from_in_list_dec
      end;
      match type of Hdec0 with
      | _ ∈ _ => apply (in_implies_event_in _ _ _ v) in Hdec0
      | _ ∉ _ => apply (@not_in_implies_event_not_in _ _ _ v) in Hdec0
      end;
      rewrite <- Hdom in Hdec0;
      clear Hdom
  end.

  (** Decompose a hypothesis of the form _ ⊢ _ →{_} _ into its components *)

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
  | delay_space ?S0 ?sensitivities ?guard ?guardb ⊢ ?σ →{Some (Event ?x ?v)} _ =>


    let Hequiv := fresh "Hequiv" in
    let Hguard := fresh "Hguard" in
    let Hdec   := fresh "Hdec" in

      decide_in_list_dec Hdec x sensitivities;
      match type of Hdec with
      | _ = false =>
        try (assert (Hguard : guard σ);
              [ apply (delay_space_inversion_output _ S0 sensitivities guard guardb σ _ _ Hstep);
                try (try unfold space_domain; simpl; solve_set);
                try (constructor; simpl; solve_set);
                fail
              | ]);
       apply delay_space_inversion_step in Hstep;
       [ destruct Hstep as [Hstep Hequiv]; clear Hdec
       | apply not_in_implies_event_not_in; solve_space_set
       ]
      | _ = true =>
        apply delay_space_inversion_sens in Hstep;
        [
        | unfold space_domain; solve_set
        | solve_space_set
        ]
      end

  | delay_space ?S0 ?sensitivities ?guard ?guardb ⊢ ?σ →{None} _ =>
      apply delay_space_inversion_step in Hstep;
      [ destruct Hstep as [Hstep Hequiv]
      | inversion 1
      ]

  (* func_space *)
  | func_space ?I ?o ?f ⊢ _ →{_} _ =>
    apply func_space_inversion in Hstep;
    [ | to_in_list_dec; simpl; repeat (auto; try compare_next); fail ];
    match type of Hstep with
    | False => contradiction
    | _ /\ _ => let Hequiv := fresh "Hequiv" in
                let Heq := fresh "Heq" in
                let Hin := fresh "Hin" in
                let Hunstable := fresh "Hunstable" in
                destruct Hstep as [Hequiv [Heq Hin]];
                simpl in Heq; simpl in Hin;
                try match type of Heq with
                | ?x = ?x -> _ => specialize (Heq eq_refl); destruct Heq as [Heq Hunstable]
                | ?x = ?y -> _ => clear Heq (* too much?? *)
                end;
                try match type of Hin with
                | ?x ∈ ?X -> _ => let Hin' := fresh "Hin" in 
                                  assert (Hin' : x ∈ X) by solve_space_set;
                                  specialize (Hin Hin'); clear Hin'
                end
    end
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

  (** Identify a hypothesis of the form _ ⊢ _ →{_} _ and decompose it 1 step *)
  Ltac step_inversion_1 := match goal with
  | [ Hstep : hide _ _ ⊢ _ →{_} _ |- _ ] =>
    step_inversion Hstep
  | [ Hstep : func_space ?I ?o ?f ⊢ _ →{_} _ |- _ ] =>
    step_inversion Hstep
  | [ Hstep : delay_space _ _ _ _ ⊢ _ →{_} _ |- _ ] =>
    step_inversion Hstep
  | [ Hstep : (?S1 ∥ ?S2) ⊢ _ →{ None } _ |- _ ] =>
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


  (** Combine hypotheses of the form state_equiv_on *)
  Lemma combine_state_equiv_on_domain : forall (S1 S2 : StateSpace name) σ σ',
    state_equiv_on (space_domain S1) (Some σ) (Some σ') ->
    state_equiv_on (space_domain S2) (Some σ) (Some σ') ->
    state_equiv_on (space_domain (S1 ∥ S2)) (Some σ) (Some σ').
  Proof.
    intros S1 S2 σ σ' Hequiv1 Hequiv2.
    intros x Hx.
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

  Lemma combine_state_equiv_on_complex : forall X1 X2 `{in_dec _ X2} σ σ' x v,
    x ∉ X1 ->
    state_equiv_on X1 (Some σ) (Some σ') ->
    state_equiv_on X2 (Some (update σ x v)) (Some σ') ->
    state_equiv_on (X1 ∪ X2) (Some (update σ x v)) (Some σ').
  Proof.
    intros ? ? ? ? ? ? ? ? Hequiv1 Hequiv2.
    intros y Hy.
    destruct (y ∈? X2); auto.
    decompose_set_structure.
    unfold update.
    compare_next; auto.
  Qed.
  Lemma combine_state_equiv_on_complex_2 : forall X0 X `{in_dec _ X} σ σ' x1 x2 v1 v2,
    x1 ∉ X0 ->
    x2 ∉ X0 ->
    state_equiv_on X0 (Some σ) (Some σ') ->
    state_equiv_on X (Some (update (update σ x1 v1) x2 v2)) (Some σ') ->
    state_equiv_on (X0 ∪ X) (Some (update (update σ x1 v1) x2 v2)) (Some σ').
  Proof.
    intros ? ? ? ? ? ? ? ? ? ? ? Hequiv1 Hequiv2.
    intros y Hy.
    destruct (y ∈? X); auto.
    decompose_set_structure.
    unfold update.
    repeat compare_next; auto.
  Qed.

  Ltac combine_state_equiv_on_complex :=
  match goal with
  | [ H0 : state_equiv_on ?X0 (Some ?σ) (Some ?σ')
    , H  : state_equiv_on ?X (Some (update ?σ ?x ?v)) (Some ?σ')
    |- _ ] =>
    let Hequiv := fresh "Hequiv" in
    assert (Hequiv : state_equiv_on (X0 ∪ X) (Some (update σ x v)) (Some σ'));
    [ apply (combine_state_equiv_on_complex X0 X σ σ' x v); auto;
        try solve_space_set
    | clear H H0
    ]
  | [ H0 : state_equiv_on ?X0 (Some ?σ) (Some ?σ')
    , H  : state_equiv_on ?X (Some (update (update ?σ ?x1 ?v1) ?x2 ?v2)) (Some ?σ')
    |- _ ] =>
    let Hequiv := fresh "Hequiv" in
    assert (Hequiv : state_equiv_on (X0 ∪ X) (Some (update (update σ x1 v1) x2 v2)) (Some σ'));
    [ apply (combine_state_equiv_on_complex_2 X0 X σ σ' x1 x2 v1 v2); auto;
        try solve_space_set
    | clear H H0
    ]

  | [ H1 : state_equiv_on (from_list ?X1) (Some ?σ1) (Some ?σ')
    , H2 : state_equiv_on (from_list ?X2) (Some ?σ2) (Some ?σ')
    |- _ ] =>
    let Hequiv := fresh "Hequiv" in
    assert (Hequiv : state_equiv_on (from_list X1 ∪ from_list X2)
                                    (Some (fun x => if in_list_dec x X1 then σ1 x else σ2 x))
                                    (Some σ'));
    [ | clear H1 H2 ]
  end. 

  Ltac standardize_state_equiv_on_set H :=
      match type of H with
      | state_equiv_on ?X _ _ =>
        let HX := fresh "HX" in
        set_to_list HX X;
        rewrite HX in H;
        clear HX
      end.

  Ltac solve_in_dom :=
  repeat match goal with
  | [ |- ?x ∈ space_domain (latch_stage_with_env _) ] =>
    rewrite dom_latch_stage_with_env
  | [ |- ?x ∈ _ ] => solve_space_set; fail
  end;
  try match goal with
  | [ |- context[ latch_to_token_flag ?l ] ] =>
    destruct l; solve_space_set
  end;
  fail.


  Ltac combine_state_equiv_on_domain :=
  match goal with
  | [ l : latch _ _
    , Hequiv : state_equiv_on ?X (Some ?σ) (Some ?σ')
    |- _  ] =>

    let Hequiv' := fresh "Hequiv" in
    assert (Hequiv' : state_equiv_on (space_domain (latch_stage_with_env l)) (Some σ) (Some σ'));
    [ let Hx := fresh "Hx" in
      intros ? Hx;
      rewrite dom_latch_stage_with_env in Hx;
      apply Hequiv;
      decompose_set_structure;
      solve_in_dom
    | clear Hequiv
    ]
  end.


  Ltac step_inversion_clean :=
  repeat (step_inversion_1;
    try combine_state_equiv_on;
    repeat match goal with
    | [ Hequiv : state_equiv_on _ _ _ |- _ ] => standardize_state_equiv_on_set Hequiv
    end;
    try (combine_state_equiv_on_complex; auto; [ solve_in_dom | ])
    ).



  End ClickTactics.
  Export ClickTactics.
  Module Structural := Structural_SS(Name).
  Import Structural.

  Existing Instance singleton_enumerable.
  Existing Instance empty_enumerable.
  Existing Instance from_list_enumerable.

  (* Ignore functional step relation 
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
  *)



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




(********************************************
*
* Proofs about wf_stage_state
*
*********************************************)

(*
  Lemma clk_not_stable : forall l σ,
    wf_stage_state l σ ->
    wf_stage_state_stable l σ ->
    latch_clk_function l σ = Bit1 ->
    σ (
*)

  Lemma flop_not_stable_old_clk : forall l σ,
    wf_stage_state l σ ->
    σ (latch_clk l) <> σ (latch_old_clk l) ->
    ~ stable (latch_flop_component l) σ.
  Proof.
    intros l σ Hwf Hneq.
    assert (Hclk : val_is_bit (σ (latch_clk l))) by solve_val_is_bit.
    assert (Hstate0 : val_is_bit (σ (latch_state0 l))) by solve_val_is_bit.
    assert (Hnot_state0 : val_is_bit (σ (latch_not_state0 l))) by solve_val_is_bit.
    dependent destruction Hclk; rename x into Hclk.
    { (* clk = 0 *)
      assert (Hstep : latch_flop_component l ⊢ σ →{None}
                        Some (update σ (latch_old_clk l) (σ (latch_clk l)))).
      { apply Hide_Neq; [ | inversion 1].
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

    { (* clk = 1 *)

      set (Hhidden := wf_hidden l σ Hwf).
      set (Hreset := wf_dp_reset_n l σ Hwf).
      simpl in Hhidden, Hreset.

      assert (Hstep : latch_flop_component l ⊢ σ
                        →{Some (Event (latch_state0 l) (σ (latch_not_state0 l)))}
                        (Some (update (update σ (latch_state0 l) (σ (latch_not_state0 l)))
                                      (latch_old_clk l) (σ (latch_clk l))))).
      { apply Hide_Neq; [ | inversion 1; subst; contradict pf; solve_space_set].
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
            { compare (σ (latch_state0 l)) (σ (latch_not_state0 l)); auto.
              2:{ symmetry; apply val_is_bit_neq; try solve_val_is_bit. }
              
              contradict Hneq. rewrite <- Hclk. symmetry.
              apply wf_clk_stable; auto.
            }
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
(*    assert (Hclk : σ (latch_clk l) = σ (latch_old_clk l)).
    { admit. } *)

    compare (σ (latch_old_clk l)) (σ (latch_clk l)).
    2:{ apply flop_not_stable_old_clk; auto. }

    (* if equal, then latch_not_state0 can step *)
    assert (Hstep : latch_flop_component l
              ⊢ σ →{Some (Event (latch_not_state0 l) (neg_value (σ (latch_state0 l ))))}
                    Some (update σ (latch_not_state0 l)
                                   (neg_value (σ (latch_state0 l))))).
    { eapply Hide_Neq.
      2:{ inversion 1; subst. contradict pf; solve_space_set. }
      apply union_step_1.
      { inversion 1; subst. contradict pf. unfold space_domain; simpl; solve_space_set. }
      2:{ intros x Hx. unfold space_domain in Hx; simpl in Hx.
          decompose_set_structure.
      }
      apply union_communicate.
      { apply driven_by_2; constructor; simpl; try (solve_space_set; fail).
        destruct l; solve_set.
      }
      2:{ apply func_output.
          { rewrite <- Heq. rewrite Heq. apply bit_neq_neg_r.
            { apply Hwf.
              rewrite dom_latch_stage_with_env. solve_space_set.
            }
          }
          { reflexivity. }
          { intros x Hx. reflexivity. }
      }
      { apply Flop_input; [ auto | | solve_space_set; destruct l; auto | intros ? ?; auto].
        left.
        set (Hhidden := wf_hidden l σ Hwf).
        set (Hreset := wf_dp_reset_n l σ Hwf).
        { destruct l; simpl; auto;
          simpl in Hhidden, Hreset; rewrite Hreset, Hhidden; simpl; auto.
        }
      }
    }
    intros [_ Hstable].
    specialize (Hstable _ _ Hstep).
    inversion Hstable; subst.
    contradict pf. simpl. solve_set.
  Qed.


  Lemma latch_flop_component_stable : forall l σ,
    wf_stage_state l σ ->
    stable (latch_flop_component l) σ <->
      (σ (latch_clk l) = σ (latch_old_clk l)
    /\ σ (latch_state0 l) = neg_value (σ (latch_not_state0 l))).
  Proof.
    intros l σ Hwf.
    split. 
    * intros Hstable.
      compare (σ (latch_clk l)) (σ (latch_old_clk l)).
      2:{ contradict Hstable. apply flop_not_stable_old_clk; auto. }
      compare (σ (latch_state0 l)) (σ (latch_not_state0 l)).
      { contradict Hstable. apply flop_not_stable_state; auto. }
      split; auto.
      symmetry; apply val_is_bit_neq; auto; try solve_val_is_bit.

    * intros [Hclk Hstate0].
      constructor; auto.
      intros ? ? Hstep.
      destruct τ as [σ' | ].
      2:{ contradict Hstep.
          intro Hstep.
          repeat match goal with
          | [ Hequiv : state_equiv_on _ _ None |- _ ] => inversion Hequiv
          | [ Hstep : _ ⊢ _ →{_} None |- _ ] =>
            inversion Hstep; subst; clear Hstep
          end; find_contradiction.
      }
      destruct e as [[x v] | ].
      + assert (Hdom : x ∈ from_list (dp_reset_n
                           :: latch_state0 l
                           :: latch_not_state0 l
                           :: latch_clk l ::nil)).
        { apply wf_space in Hstep; auto. 
          destruct l; simpl in Hstep; decompose_set_structure; solve_space_set.
        }
        decompose_set_structure.
        ++ constructor. simpl. destruct l; simpl; solve_set.
        ++ repeat step_inversion_1.
           apply flop_inversion_output in Hstep1.
           2:{ solve_all_disjoint. }
           2:{ destruct l; simpl; destruct Hwf; auto. }
           2:{ destruct l; simpl; destruct Hwf; auto. }
           contradict Hclk.
           destruct Hstep1 as [Hclk1 [Hclk2 _]].
           rewrite Hclk1. auto.
        ++ repeat step_inversion_1.
           clear Hin.
           contradict Hunstable.
           simpl in Hstate0.
           rewrite Hstate0.
           rewrite val_is_bit_neg_neg; solve_val_is_bit.
        ++ constructor. simpl; solve_set.

      + do 3 step_inversion_1.
        ++ repeat step_inversion_1.
           { inversion Hstep; subst; auto. find_contradiction. }
        ++ inversion Hstep.
        ++ repeat step_inversion_1.
           assert (Hstable : stable (func_space nil (latch_hidden l) (fun _ => Num 1)) σ).
           { apply func_stable_equiv.
             { solve_set. }
             { destruct Hwf; auto. }
           }
           (* Contradiction *)
           destruct Hstable as [_ Hstable].
           clear Hin.
           absurd (event_in ∅ (Some (Event (latch_hidden l) Bit1))).
           { inversion 1; subst; find_contradiction. }
           { eapply Hstable.
             apply func_output; auto.
             intros x Hx; reflexivity.
           }
  Qed.


  Lemma delay_space_stable : forall S sens guard guardb (σ : state name),
    stable S σ ->
    well_formed (delay_space S sens guard guardb) ->
    stable (delay_space S sens guard guardb) σ.
         
  Proof.
    intros S sens guard guardb σ [Hwf Hstable] Hwf'.
    constructor; auto. 
    intros e τ Hstep.
    inversion Hstep; subst; auto.
    * constructor. simpl. solve_set.
    * constructor; simpl; solve_set.
    * apply Hstable in H. inversion H; subst.
    * apply Hstable in H0. inversion H0; subst.
      absurd (x ∈ space_input S ∩ space_output S); try solve_set.
      apply space_input_output; auto.
  Qed.

  Lemma left_ack_stable : forall l σ,
    σ (ack (latch_input l)) = match latch_to_token_flag l with
                              | Token => neg_value (σ (latch_state0 l))
                              | NonToken => σ (latch_state0 l)
                              end ->
    stable (latch_left_ack_component l) σ.
  Proof.
    intros.
    apply delay_space_stable; auto.
    2:{ apply latch_left_ack_component_well_formed. }
    apply func_stable_equiv; auto.
    solve_space_set.
  Qed.


  Lemma left_ack_stable_inversion : forall l σ,
    stable (latch_left_ack_component l) σ ->
    σ (latch_clk l) = Bit0 ->
    σ (latch_not_state0 l) = neg_value (σ (latch_state0 l)) ->
    σ (ack (latch_input l)) = match latch_to_token_flag l with
                              | Token => neg_value (σ (latch_state0 l))
                              | NonToken => σ (latch_state0 l)
                              end.
  Proof.
    intros ? ? [Hwf Hstable] Hclk Hstate.
    match goal with
    | [ |- ?x = ?y ] => compare x y; auto; remember y as z
    end; auto.
    (* <> *)
    assert (Hstep : latch_left_ack_component l ⊢ σ →{Some (Event (ack (latch_input l)) z)}
                       Some (update σ (ack (latch_input l)) z)).
    { apply delay_space_output; auto.
      { apply func_output; auto.
        2:{ intros x Hx. reflexivity. }
        subst; auto.
      }
      { simpl. solve_space_set. }
      { intros x Hx. decompose_set_structure. }
    }
    specialize (Hstable _ _ Hstep).
    inversion Hstable; subst.
    contradict pf. simpl; solve_set.
  Qed.


  Lemma σR_wf : forall l,
    wf_stage_state l (σR l).
  Proof.
    intros l.
    assert (Hbit : forall x, x ∈ space_domain (latch_stage_with_env l) -> val_is_bit (σR l x)).
    { intros x Hx. unfold σR.
        repeat (compare_next; try constructor);
          destruct l; try constructor.
    }
    assert (Hhidden : σR l (latch_hidden l) = Bit1).
    { unfold σR; repeat compare_next; constructor. }
(*    assert (Hclk : σR l (latch_state0 l) = σR l (latch_not_state0 l) ->
                   σR l (latch_clk l) = σR l (latch_old_clk l)).
    { unfold σR. simpl. reduce_eqb. }
*)
    split; auto.
    * unfold σR; simpl; reduce_eqb; auto.
    * unfold σR; simpl; reduce_eqb. intros.
      destruct l; auto.
    * unfold σR; simpl; reduce_eqb. intros.
      destruct l; auto.
    * unfold σR; simpl; reduce_eqb. intros.
      destruct l; auto.
    * unfold σR; simpl; reduce_eqb.
  Qed.
  Lemma σR_wf_stable : forall l,
    wf_stage_state_stable l (σR l).
  Proof.
    split.
    { intros Hstable.
      apply latch_flop_component_stable.
      { apply σR_wf. }
      split; unfold σR; simpl; reduce_eqb; auto.
      destruct l; auto.
    }
    { (* When l is Odd, left_env_component is stable *)
      (* When l is Even, latch_left_ack_component is stable, a contradiction *)
      intros Hstable; destruct l as [O|E].
      + (* l = odd *)
        apply func_stable_equiv.
        { solve_space_set. }
         unfold σR; simpl; reduce_eqb; auto.
      + (* l = even *)
        contradict Hstable.
        apply delay_space_stable; auto.
        2:{ apply latch_left_ack_component_well_formed. }
        apply func_stable_equiv; try solve_space_set.
        unfold σR; simpl; reduce_eqb; auto.
    }
    { intros Hstable. apply latch_flop_component_stable.
      { apply σR_wf. }
      split; unfold σR; simpl; reduce_eqb; auto.
      destruct l; auto.
    }
    { (* When l is odd, right_env_component is stable *)
      (* When l is even, latch_right_req_component is stable, a contradiction *)
      intros Hstable; destruct l as [O|E].
      + (* l = odd *)
        apply func_stable_equiv.
        { solve_space_set. }
        unfold σR; simpl; reduce_eqb; auto.
 
      + (* l = even *)
        contradict Hstable.
        apply func_stable_equiv.
        { solve_space_set. }
        unfold σR; simpl; reduce_eqb; auto.
    }
(*
    { intros Hf Hclk.
      destruct l as [O|E].
        2:{ contradict Hf.
            unfold latch_clk_function, tok_clk_defn.
            unfold σR; simpl; reduce_eqb.
        }
      split; [ | split; [ | split; [ | split]]].
      + apply func_stable_equiv.
        { solve_space_set. }
        { unfold σR. simpl. reduce_eqb; auto. }
      + apply func_stable_equiv.
        { solve_space_set. }
        { unfold σR; simpl; reduce_eqb; auto. }
      + apply delay_space_stable; auto.
        2:{ solve_wf. }
        apply func_stable_equiv.
        { solve_space_set. }
        { unfold σR; simpl; reduce_eqb; auto. }
      + apply func_stable_equiv.
        { solve_space_set. }
        { unfold σR; simpl; reduce_eqb; auto. }
      + apply latch_flop_component_stable.
        { apply σR_wf. }
        { split; unfold σR; simpl; reduce_eqb; auto. }
    }
*)

  Qed.

  Lemma latch_clk_function_equiv : forall σ' σ l,
    state_equiv_on (from_list (ctrl_reset_n :: latch_state0 l :: req (latch_input l) :: ack (latch_output l) :: nil))
                   (Some σ)
                   (Some σ') ->
    latch_clk_function l σ = latch_clk_function l σ'.
  Proof.
    intros ? ? ? Hequiv.
    destruct l; unfold latch_clk_function; [ unfold clk_defn | unfold tok_clk_defn ].
    * repeat (rewrite_state_equiv; try solve_in_dom; auto).
    * repeat (rewrite_state_equiv; try solve_in_dom; auto).
  Qed.


Lemma latch_clk_function_Bit1_l_req : forall l σ,
    σ ctrl_reset_n = Bit1 ->
    val_is_bit (σ (req (latch_input l))) ->
    val_is_bit (σ (ack (latch_output l))) ->
    val_is_bit (σ (latch_state0 l)) ->

    latch_clk_function l σ = Bit1 ->
    σ (req (latch_input l)) = if_token l (σ (latch_state0 l)).

Proof.
  intros [O | E] σ Hreset Hbit1 Hbit2 Hbit3 Hf.
  * unfold latch_clk_function in Hf. simpl in Hf.
    unfold clk_defn in Hf.
    simpl in Hreset. rewrite Hreset in Hf. simpl in Hf.
    simpl.
    inversion Hbit1 as [Hbit1' | Hbit1']; rewrite <- Hbit1' in Hf; simpl in Hf;
    inversion Hbit3 as [Hbit3' | Hbit3']; rewrite <- Hbit3' in Hf; simpl in Hf; auto;
    inversion Hbit2 as [Hbit2' | Hbit2']; rewrite <- Hbit2' in Hf; simpl in Hf; auto.

  * unfold latch_clk_function in Hf. simpl in Hf.
    unfold tok_clk_defn in Hf.
    simpl in Hreset. rewrite Hreset in Hf. simpl in Hf.
    simpl.
    inversion Hbit1 as [Hbit1' | Hbit1']; rewrite <- Hbit1' in Hf; simpl in Hf;
    inversion Hbit3 as [Hbit3' | Hbit3']; rewrite <- Hbit3' in Hf; simpl in Hf; auto;
    inversion Hbit2 as [Hbit2' | Hbit2']; rewrite <- Hbit2' in Hf; simpl in Hf; auto.
Qed.
Lemma latch_clk_function_Bit1_r_ack : forall l σ,
    σ ctrl_reset_n = Bit1 ->
    val_is_bit (σ (req (latch_input l))) ->
    val_is_bit (σ (ack (latch_output l))) ->
    val_is_bit (σ (latch_state0 l)) ->

    latch_clk_function l σ = Bit1 ->
    σ (ack (latch_output l)) = σ (latch_state0 l).
Proof.
  intros [O | E] σ Hreset Hbit1 Hbit2 Hbit3 Hf.
  * unfold latch_clk_function in Hf. simpl in Hf.
    unfold clk_defn in Hf.
    simpl in Hreset. rewrite Hreset in Hf. simpl in Hf.
    simpl.
    inversion Hbit1 as [Hbit1' | Hbit1']; rewrite <- Hbit1' in Hf; simpl in Hf;
    inversion Hbit3 as [Hbit3' | Hbit3']; rewrite <- Hbit3' in Hf; simpl in Hf; auto;
    inversion Hbit2 as [Hbit2' | Hbit2']; rewrite <- Hbit2' in Hf; simpl in Hf; auto.

  * unfold latch_clk_function in Hf. simpl in Hf.
    unfold tok_clk_defn in Hf.
    simpl in Hreset. rewrite Hreset in Hf. simpl in Hf.
    simpl.
    inversion Hbit1 as [Hbit1' | Hbit1']; rewrite <- Hbit1' in Hf; simpl in Hf;
    inversion Hbit3 as [Hbit3' | Hbit3']; rewrite <- Hbit3' in Hf; simpl in Hf; auto;
    inversion Hbit2 as [Hbit2' | Hbit2']; rewrite <- Hbit2' in Hf; simpl in Hf; auto.
Qed.

  Section step_wf_state_lemma.

    Variable l : latch even odd.
    Context (σ σ' : state name).
    Hypothesis Hwf : wf_stage_state l σ.

    Definition step_wf_state_lemma_defn x :=
      forall v,
      latch_stage_with_env l ⊢ σ →{Some (Event x v)} Some σ' ->
      wf_stage_state l σ'.

    Lemma step_wf_state_lemma_defn_l_req : step_wf_state_lemma_defn (req (latch_input l)).
    Proof.
      intros v Hstep.
      step_inversion_clean.
      combine_state_equiv_on_domain.
      constructor.
      + (* val_is_bit *)
        intros y HY.
        rewrite_state_equiv; auto.
        repeat compare_next; auto; try solve_val_is_bit.
        eapply wf_all_bits; eauto.

      + (* ctrl_reset_n *)
        rewrite_state_equiv; try solve_in_dom.
        erewrite wf_ctrl_reset_n; eauto.

      + (* dp_reset_n *)
        rewrite_state_equiv; try solve_in_dom.
        erewrite wf_dp_reset_n; eauto.        

      + (* latch_hidden *)
        rewrite_state_equiv; try solve_in_dom.
        rewrite wf_hidden; auto.

      + (* latch_clk vs latch_state0 *)
        repeat (rewrite_state_equiv; try solve_in_dom).
        simpl; reduce_eqb.
        apply wf_clk_stable; auto.

      + (* clk component is unstable *)
        repeat (rewrite_state_equiv; try solve_in_dom).
        simpl; reduce_eqb.
        intros Hf Hclk.
        replace (latch_clk_function l σ')
              with (latch_clk_function l (update σ (local_name l "l_req") v))
              in Hf.
        2:{ apply latch_clk_function_equiv.
            intros y Hy.
            apply Hequiv.
            decompose_set_structure;
            solve_in_dom.
        }
        clear Hin.
        destruct Hin0 as [Hclk_function | Hclk_function].
        2:{ apply wf_clk_unstable; auto.
            rewrite Hclk_function; auto. }
        { rewrite <- Hclk_function in Hclk.
          apply left_env_component_unstable; auto.
          rewrite <- (val_is_bit_neg_neg (σ (ack (latch_input l)))); try solve_val_is_bit.
          symmetry.
          apply val_is_bit_neq; [ | solve_val_is_bit | auto].
          { assert (Hbit : val_is_bit (σ (ack (latch_input l)))) by solve_val_is_bit.
            inversion Hbit as [Hbit' | Hbit']; simpl; rewrite <- Hbit'; auto with click.
          }
        }

     + repeat (rewrite_state_equiv; try solve_in_dom).
       simpl. reduce_eqb.
       intros Hv; contradict Heq; subst.
       apply bit_neq_neg_r; solve_val_is_bit.
    
     + repeat (rewrite_state_equiv; try solve_in_dom).
       simpl. reduce_eqb.
       intros Hv.
       apply left_env_component_unstable; auto.
       { apply val_is_bit_neq in Hunstable; try solve_val_is_bit.
         simpl.
         rewrite <- Hunstable.
         rewrite val_is_bit_neg_neg; auto; solve_val_is_bit.
       }

      +
Abort (*
    repeat (rewrite_state_equiv; try solve_in_dom).
        simpl.
        intros Hclk.
        destruct Hin0; auto.
        Search latch_clk_function.
        rewrite (latch_clk_function_equiv σ).
        2:{ intros y Hy. rewrite_state_equiv; auto; try solve_in_dom.
            compare_next; auto.
            clear Hin.
            apply val_is_bit_neq; try solve_val_is_bit.
            auto
        apply wf_clk_fn_stable.
    Unshelve. exact (fun _ => true).
    Qed.
*).

    Lemma step_wf_state_lemma_defn_l_ack : step_wf_state_lemma_defn (ack (latch_input l)).
    Proof.
      intros v Hstep.
      step_inversion_clean.
      combine_state_equiv_on_domain.

      clear Hequiv0.
      constructor.

      + (* val_is_bit *) intros y Hy.
        rewrite_state_equiv; auto.
        compare_next; auto;
        try solve_val_is_bit.
        eapply wf_all_bits; eauto.

      + (* ctrl_reset_n *)
        rewrite_state_equiv; try solve_in_dom.
        erewrite wf_ctrl_reset_n; eauto.

      + (* dp_reset_n *)
        rewrite_state_equiv; try solve_in_dom.
        erewrite wf_dp_reset_n; eauto.

      + (* latch_hidden *)
        rewrite_state_equiv; try solve_in_dom.
        erewrite wf_hidden; eauto.

      + (* clk vs state0 *)
        repeat (rewrite_state_equiv; try solve_in_dom).
        simpl.
        apply wf_clk_stable; auto.

      + intros _ _.
        repeat (rewrite_state_equiv; try solve_in_dom).
        simpl. 
        destruct Hguard as [_ Hguard].
        simpl in Hguard.
        rewrite Hguard.
        rewrite val_is_bit_neg_neg; try solve_val_is_bit.

      + intros _.
        repeat (rewrite_state_equiv; try solve_in_dom).
        simpl. 
        destruct Hguard as [_ Hguard].
        simpl in Hguard.
        rewrite Hguard.
        rewrite val_is_bit_neg_neg; try solve_val_is_bit.

      + repeat (rewrite_state_equiv; try solve_in_dom).
        simpl.
        apply left_component_stable; auto.

      + repeat (rewrite_state_equiv; try solve_in_dom).
        simpl.
        admit.
    Unshelve.
(*    exact (fun _ => true).*)
    Admitted.

    Lemma step_wf_state_lemma_defn_r_req : step_wf_state_lemma_defn (req (latch_output l)).
    Proof.
      intros v Hstep.
      step_inversion_clean.
      combine_state_equiv_on_domain.

      constructor.
      + (* val_is_bit *) intros y Hy.
        rewrite_state_equiv; auto.
        compare_next;
        try solve_val_is_bit.
        eapply wf_all_bits; eauto.

      + (* ctrl_reset_n *)
        rewrite_state_equiv; try solve_in_dom.
        erewrite wf_ctrl_reset_n; eauto.
      + (* dp_reset_n *)
        rewrite_state_equiv; try solve_in_dom.
        erewrite wf_dp_reset_n; eauto.
      + (* hidden *)
        rewrite_state_equiv; try solve_in_dom.
        erewrite wf_hidden; eauto.

      + (* clk vs state0 *)
        repeat (rewrite_state_equiv; try solve_in_dom).
        apply wf_clk_stable; auto.
      + repeat (rewrite_state_equiv; try solve_in_dom).
        simpl. clear Hin0.
        erewrite (latch_clk_function_equiv _); eauto.
        { apply wf_clk_unstable; auto. }
        { intros y Hy.
          decompose_set_structure; rewrite_state_equiv; auto; solve_in_dom.
        }
      + repeat (rewrite_state_equiv; try solve_in_dom).
        apply left_env_component_unstable; auto.
      + repeat (rewrite_state_equiv; try solve_in_dom).
        apply left_component_stable; auto.
      + admit.

    Unshelve. exact (fun _ => true).
    Admitted.

    Lemma step_wf_state_lemma_defn_r_ack : step_wf_state_lemma_defn (ack (latch_output l)).
    Proof.
      intros v Hstep.
      step_inversion_clean.
      combine_state_equiv_on_domain.

      clear Hin.

      constructor.
      + (* val_is_bit *) intros y Hy.
        rewrite_state_equiv; auto.
        compare_next;
        try solve_val_is_bit.
        eapply wf_all_bits; eauto.

      + (* ctrl_reset_n *)
        rewrite_state_equiv; try solve_in_dom.
        erewrite wf_ctrl_reset_n; eauto.
      + (* dp_reset_n *)
        rewrite_state_equiv; try solve_in_dom.
        erewrite wf_dp_reset_n; eauto.
      + (* hidden *)
        rewrite_state_equiv; try solve_in_dom.
        erewrite wf_hidden; eauto.
      + (* clk vs state0 *)
        repeat (rewrite_state_equiv; try solve_in_dom); simpl.
        apply wf_clk_stable; auto.
      + repeat (rewrite_state_equiv; try solve_in_dom); simpl.

        intros H_clk_fn Hclk.
        apply left_component_stable; auto.
        transitivity (σ' (req (latch_input l))).
        { rewrite_state_equiv; simpl; auto. solve_in_dom. }
        transitivity (if_token l (σ' (latch_state0 l))).
        2:{ rewrite_state_equiv; simpl; auto. solve_in_dom. }
        apply latch_clk_function_Bit1_l_req; auto;
          try (rewrite_state_equiv; try solve_in_dom; simpl; auto;
                try reduce_eqb; subst; try solve_val_is_bit; fail).
        { rewrite_state_equiv; try solve_in_dom; simpl; reduce_eqb.
          eapply wf_ctrl_reset_n; eauto.
        }

      + repeat (rewrite_state_equiv; try solve_in_dom); simpl.
        apply left_env_component_unstable; auto.
      + repeat (rewrite_state_equiv; try solve_in_dom); simpl.
        apply left_component_stable; auto.
      + admit.

    Unshelve. exact (fun _ => true).
    Admitted.

    Lemma step_wf_state_lemma_defn_clk : step_wf_state_lemma_defn (latch_clk l).
    Proof.
      intros v Hstep.
      step_inversion_clean.
      clear Hin.
      combine_state_equiv_on_complex; try (simpl; solve_space_set; fail).
      destruct Hwf.
      apply flop_inversion_clk in Hstep3.
      2:{ solve_all_disjoint. }
      2:{ destruct l; simpl; auto. }
      2:{ destruct l; simpl; auto. }
      destruct Hstep3 as [Hequiv' Hstep3].
      combine_state_equiv_on.
      standardize_state_equiv_on_set Hequiv0.
      combine_state_equiv_on_domain.

      subst.
      assert (Hv : val_is_bit (latch_clk_function l σ)).
      { 
        assert (Hreq : val_is_bit (σ (req (latch_input l)))) by solve_val_is_bit.
        assert (Hack : val_is_bit (σ (ack (latch_output l)))) by solve_val_is_bit.
        assert (Hstate0 : val_is_bit (σ (latch_state0 l))) by solve_val_is_bit.

        unfold latch_clk_function.
        unfold tok_clk_defn, clk_defn; destruct l; simpl;
          simpl in wf_ctrl_reset_n0; rewrite wf_ctrl_reset_n0; simpl;
          inversion Hreq; simpl;
          inversion Hstate0; simpl;
          inversion Hack; simpl;
          constructor.
      }

      constructor.
      + (* val_is_bit *) intros y Hy.
        rewrite_state_equiv.
        destruct (Dec y (latch_clk l)).
        { rewrite e. simpl. reduce_eqb; auto. }
        { simpl in n. reduce_eqb. solve_val_is_bit. }
      + rewrite_state_equiv; try solve_in_dom.
        simpl; auto.
      + rewrite_state_equiv; try solve_in_dom.
        simpl; auto.
      + rewrite_state_equiv; try solve_in_dom.
        simpl; auto.
      + (* clk vs state0 *)
        repeat (rewrite_state_equiv; try solve_in_dom); simpl.
        reduce_eqb.

        intros Hstate0 Hv'.

        (* Because the clock component is unstable and latch_clk_function = 1, it must be the
             case that the flop component is stable *)

        symmetry in Hstate0.
        contradict Hstate0.

        simpl in *.
        rewrite wf_clk_unstable0; auto.
        { apply bit_neq_neg_r. apply wf_all_bits0. solve_in_dom. }
        { assert (Hbit : val_is_bit (σ (local_name l "clk"))) by solve_val_is_bit.
          inversion Hbit as [ | Hbit']; auto.
          contradict Hunstable.
          rewrite <- Hbit'; auto.
        }

      + (* clk vs state0 *)
        repeat (rewrite_state_equiv; try solve_in_dom); simpl.
        reduce_eqb.
        intros Hfn' Hfn.
        clear Hdec.

        contradict Hfn.
        rewrite (latch_clk_function_equiv σ').
        2:{ intros y Hy. rewrite <- Hequiv.
            { unfold update. decompose_set_structure; auto. }
            { decompose_set_structure; solve_in_dom. }
        }
        rewrite Hfn'; inversion 1.

     + repeat (rewrite_state_equiv; try solve_in_dom); simpl. auto.
     + repeat (rewrite_state_equiv; try solve_in_dom); simpl. auto.

     + admit.
    Unshelve. exact (fun _ => true).
    Admitted.

  Lemma step_wf_state_lemma : forall e,
    latch_stage_with_env l ⊢ σ →{Some e} Some σ' ->
    wf_stage_state l σ'.
  Proof.
    intros [x v] Hstep.
    assert (Hx : x ∈ space_input (latch_stage_with_env l) ∪ space_output (latch_stage_with_env l)).
    { eapply wf_space; eauto. }
    rewrite latch_stage_with_env_input, latch_stage_with_env_output in Hx.
    simpl in Hx.

    decompose_set_structure.        
    * (* l_req *) admit (*eapply step_wf_state_lemma_defn_l_req; eauto.*).
    * (* l_ack *) eapply step_wf_state_lemma_defn_l_ack; eauto.
    * (* r_req *) eapply step_wf_state_lemma_defn_r_req; eauto.
    * (* r_ack *) eapply step_wf_state_lemma_defn_r_ack; eauto.
    * (* clk *) eapply step_wf_state_lemma_defn_clk; eauto.
  Admitted.

 End step_wf_state_lemma.

(*
Lemma step_wf_stable_lemma : forall l σ e σ',
    wf_stage_state l σ ->
    wf_stage_state_stable l σ ->
    latch_stage_with_env l ⊢ σ →{Some e} Some σ' ->
    wf_stage_state_stable l σ'.
Proof.

    intros l σ [x v] σ' Hwf Hwf' Hstep.
    assert (Hx : x ∈ space_input (latch_stage_with_env l) ∪ space_output (latch_stage_with_env l)).
    { eapply wf_space; eauto. }
    rewrite latch_stage_with_env_input, latch_stage_with_env_output in Hx.
    simpl in Hx.

    assert (Hwf'' : wf_stage_state l σ').
    { eapply step_wf_state_lemma; eauto. }

    decompose_set_structure.

    * (* l_req *)
      step_inversion_clean.
      combine_state_equiv_on_domain.
      clear Hin.
      subst.
      constructor.

      + intros Hstable.
        contradict Hstable.
        apply delay_space_stable.
        2:{ solve_wf. unfold space_domain; simpl.  solve_set. }

        assert (~ stable (latch_left_ack_component l) σ).
        { intros Hstable. Search stable delay_space.
          

        assert (stable (func_space (latch_state0 l::nil) (ack (latch_input l))
                  (fun σ0 => match latch_to_token_flag l with
                             | Token => neg_value (σ0 (latch_state0 l))
                             | NonToken => σ0 (latch_state0 l)
                             end))
                  σ).
        { apply func_stable_equiv. { solve_space_set. }
Admitted.
*)


Lemma neg_value_inj : forall v1 v2, val_is_bit v1 -> val_is_bit v2 ->
    neg_value v1 = neg_value v2 -> v1 = v2.
Proof.
    intros v1 v2 Hbit1 Hbit2 Heq.
    rewrite <- (val_is_bit_neg_neg v1); auto.
    apply val_is_bit_neg_inversion; auto.
Qed.
Lemma latch_clk_function_fall : forall l σ σ',
    state_equiv_on (from_list (ctrl_reset_n :: req (latch_input l) :: ack (latch_output l) :: nil))
                   (Some σ) (Some σ') ->
    σ ctrl_reset_n = Bit1 ->
    val_is_bit (σ (req (latch_input l))) ->
    val_is_bit (σ (ack (latch_output l))) ->
    val_is_bit (σ (latch_state0 l)) ->
    val_is_bit (σ' (latch_state0 l)) ->
    σ (latch_state0 l) <> σ' (latch_state0 l) ->
    latch_clk_function l σ = Bit1 ->
    latch_clk_function l σ' = Bit0.
  Proof.
    intros ? ? ? Hequiv Hreset Hreq Hack Hstate0_bit Hstate0_bit' Hstate0 Hf.
    unfold latch_clk_function, clk_defn, tok_clk_defn in *.
    rewrite <- (Hequiv ctrl_reset_n) in *; try solve_space_set.
    rewrite <- (Hequiv (req (latch_input l))); try solve_space_set.
    rewrite <- (Hequiv (ack (latch_output l))); try solve_space_set.

    rewrite Hreset in *.
    apply val_is_bit_neq in Hstate0; auto.
    rewrite <- Hstate0.
    simpl in *.
    
    inversion Hreq as [Hbit | Hbit]; rewrite <- Hbit in Hf; simpl in *; clear Hbit;
    inversion Hstate0_bit as [Hbit | Hbit]; rewrite <- Hbit in Hf; simpl in *; clear Hbit;
    inversion Hack as [Hbit | Hbit]; rewrite <- Hbit in Hf; simpl in *; clear Hbit;
    auto;
    destruct l; auto; find_contradiction.
Qed.

  Lemma step_wf_state_eps : forall l σ σ',
    wf_stage_state l σ ->
    latch_stage_with_env l ⊢ σ →{None} Some σ' ->
    wf_stage_state l σ'.
  Proof.
    intros l σ σ' Hwf Hstep.
(*
    step_inversion_clean.
    * (* Flop None *)
      inversion Hstep as [ | | | | | ? Hclk Hold_clk  Hequiv | ]; subst; clear Hstep.
      standardize_state_equiv_on_set Hequiv.
      combine_state_equiv_on_complex.
      { simpl; solve_space_set. }
      combine_state_equiv_on_domain.
      constructor.
      + (* val_is_bit *) intros y Hy.
        rewrite_state_equiv; auto.
        compare_next; auto; try solve_val_is_bit.
        eapply wf_all_bits; eauto.
      + rewrite_state_equiv; try solve_in_dom.
        simpl; auto.
        eapply wf_ctrl_reset_n; eauto.
      + rewrite_state_equiv; try solve_in_dom.
        simpl; auto.
        eapply wf_dp_reset_n; eauto.
      + rewrite_state_equiv; try solve_in_dom.
        simpl; auto.
        apply wf_hidden; auto.
      + (* clk vs state0 *)
        repeat (rewrite_state_equiv; try solve_in_dom); simpl.
        reduce_eqb.
      + repeat (rewrite_state_equiv; try solve_in_dom); simpl.
        intros Hf Hclk'.
        apply wf_clk_unstable; auto.
        rewrite (latch_clk_function_equiv σ'); auto.
        { intros y Hy. decompose_set_structure; rewrite_state_equiv; simpl; auto; solve_in_dom. }
      + repeat (rewrite_state_equiv; try solve_in_dom); simpl.
        apply left_env_component_unstable; auto.
      + repeat (rewrite_state_equiv; try solve_in_dom); simpl.
        apply left_component_stable; auto.

    * (* flop hidden *)
      clear Hin.
      contradict Hunstable.
      symmetry; apply wf_hidden; auto.

    * (* ctrl_reset_n *) find_contradiction.
    * (* dp_reset_n *) find_contradiction.
    * (* state0 *) clear Hin Hdec.
      inversion Hstep0; subst; find_contradiction; clear Hstep0.
      repeat combine_state_equiv_on.
      combine_state_equiv_on_complex.
      { simpl; solve_space_set. }
      clear H4.
      combine_state_equiv_on_domain.
      (* Simplify H3 *)
      assert (Hor : σ (latch_state0 l) = σ(latch_not_state0 l) \/
             σ (latch_not_state0 l) = update σ (latch_not_state0 l) (neg_value (σ (latch_state0 l)))
                                        (latch_not_state0 l)).
      { simpl; destruct l; unfold latch_to_token_flag in H3;
          unfold update in H3;
          rewrite wf_hidden in H3; auto;
          erewrite wf_dp_reset_n in H3; eauto.
      }
      clear H3.
      assert (Hstate0 : σ (latch_state0 l) = σ (latch_not_state0 l)).
      { apply val_is_bit_neq in Hunstable; try solve_val_is_bit.
        simpl; rewrite <- Hunstable.
        rewrite val_is_bit_neg_neg; try solve_val_is_bit.
      }
      constructor.
      + (* val_is_bit *) intros y Hy.
        rewrite_state_equiv; auto.
        compare_next; auto; try solve_val_is_bit.
        eapply wf_all_bits; eauto.
      + rewrite_state_equiv; try solve_in_dom.
        simpl; auto.
        eapply wf_ctrl_reset_n; eauto.
      + rewrite_state_equiv; try solve_in_dom.
        simpl; auto.
        eapply wf_dp_reset_n; eauto.
      + rewrite_state_equiv; try solve_in_dom.
        simpl; auto.
        apply wf_hidden; auto.
      + (* clk vs state0 *)
        repeat (rewrite_state_equiv; try solve_in_dom); simpl.
        reduce_eqb.
        intros.
        apply wf_clk_stable; auto.
      + repeat (rewrite_state_equiv; try solve_in_dom); simpl. reduce_eqb.
        intros Hf Hclk'.
        rewrite val_is_bit_neg_neg; try solve_val_is_bit.

      + repeat (rewrite_state_equiv; try solve_in_dom); simpl.
        reduce_eqb.
        intros.
        rewrite val_is_bit_neg_neg; try solve_val_is_bit.
      + repeat (rewrite_state_equiv; try solve_in_dom); simpl. reduce_eqb.
        intros.
        rewrite val_is_bit_neg_neg; try solve_val_is_bit.

    * (* state0 *)
      About flop_inversion_output.
      apply flop_inversion_output in Hstep1; auto.
      2:{ solve_all_disjoint. }
      2:{ destruct l; [ apply wf_hidden | eapply wf_dp_reset_n ]; eauto. }
      2:{ destruct l; [ eapply wf_dp_reset_n | apply wf_hidden ]; eauto. }
      destruct Hstep1 as [Hclk [Hold_clk [Hv Hequiv]]].
      combine_state_equiv_on_complex.
      { simpl; solve_space_set. }
      combine_state_equiv_on_complex.
      combine_state_equiv_on_domain.

      unfold update in Hin2. reduce_eqb.
      unfold update in Hin. reduce_eqb.
      unfold update in Hin0. reduce_eqb.


      (* Restate Hin0 *)
      assert (Hin0' : σ (ack (latch_input l)) = if_token l (neg_value (σ (latch_state0 l)))
                   \/ v = σ (latch_state0 l)).
      { destruct Hin0 as [Hin0 | Hin0]; unfold if_token.
        { simpl. rewrite <- Hin0.
          left.
          destruct l; auto. simpl.
          rewrite val_is_bit_neg_neg; solve_val_is_bit.
        }
        { simpl. destruct l; simpl; simpl in Hin0; right; auto.
          apply neg_value_inj; auto; subst; try solve_val_is_bit.
        }
      }
      clear Hin0.

      compare (σ (latch_state0 l)) (σ (latch_not_state0 l)).
      { (* equal *)
        contradict Hold_clk.
        apply wf_clk_stable; auto.
      }
      { (* not equal *)
        (* This means that latch_clk_function l σ = Bit1 but latch_clk_function l σ = Bit0 *)

(*        assert (σ (latch_clk l) = Bit1 -> latch_clk_function l σ = Bit1) by admit.*)

        destruct Hin as [Hin | Hin]; auto.
        2:{ subst; auto; find_contradiction. }
        destruct Hin0' as [Hin0 | Hin0]; auto.
        2:{ subst; auto; find_contradiction. }
        destruct Hin2 as [Hin2 | Hin2]; auto.
        2:{ apply neg_value_inj in Hin2; subst; try solve_val_is_bit.
            find_contradiction.
        }

        destruct Hin1 as [Hin1 | Hin1]; auto.
        2:{ (* latch_clk_function σ = Bit0... but also latch_clk_function (update σ state0 v) = Bit0... *)
            (* since σ state0 <> σ not_state0, it should be the case that clk_component is stable... *)
Print wf_stage_state.
        (* If latch_clk l <> latch_old_clk l then latch_clk_function = latch_clk ... *)
eaj;foehgroiefjoefije;woh    
contradict Hin1.
    latch_clk_function_fall

            admit (* true since v = latch_not_state0 = neg_value (latch_not_state0) *).
        }

        simpl in Hclk.
        rewrite Hclk in Hin1.
        Search latch_clk_function Bit1.
        apply latch_clk_function_Bit1_l_req in Hin1; try solve_val_is_bit.
        2:{ eapply wf_ctrl_reset_n; eauto. }
        
        assert (Henv : σ (ack (latch_input l)) = neg_value (σ (req (latch_input l)))).
        { rewrite Hin1. rewrite Hin0. destruct l; auto. }

      constructor.
      + (* val_is_bit *) intros y Hy.
        rewrite_state_equiv; auto.
        compare_next; auto; try solve_val_is_bit.
        compare_next; auto; try solve_val_is_bit.
        eapply wf_all_bits; eauto.
      + rewrite_state_equiv; try solve_in_dom.
        simpl; auto.
        eapply wf_ctrl_reset_n; eauto.
      + rewrite_state_equiv; try solve_in_dom.
        simpl; auto.
        eapply wf_dp_reset_n; eauto.
      + rewrite_state_equiv; try solve_in_dom.
        simpl; auto.
        apply wf_hidden; auto.
      + (* clk vs state0 *)
        repeat (rewrite_state_equiv; try solve_in_dom); simpl.
        reduce_eqb.
        intros; auto.
      + repeat (rewrite_state_equiv; try solve_in_dom); simpl.
        intros Hf Hclk'. reduce_eqb.
      + repeat (rewrite_state_equiv; try solve_in_dom); simpl. reduce_eqb.
        intros Hl.
        contradict Henv.
        { simpl; rewrite Hl. Search (_ <> neg_value _).
          apply bit_neq_neg_r. solve_val_is_bit.
        }

      + repeat (rewrite_state_equiv; try solve_in_dom); simpl. reduce_eqb.
        intros Hl.
        contradict Hin1.
        simpl; rewrite Hl. subst.
        destruct l; auto.
        simpl. unfold if_token. simpl.
        intros Heq. apply neg_value_inj in Heq; try solve_val_is_bit.

  Unshelve. exact (fun _ => true).

*)
 
  Admitted.

  Lemma step_wf_stable_eps : forall l σ σ',
    wf_stage_state l σ ->
    wf_stage_state_stable l σ ->
    latch_stage_with_env l ⊢ σ →{None} Some σ' ->
    wf_stage_state_stable l σ'.
  Admitted.
      
  Lemma step_wf_state : forall l tr σ,
    latch_stage_with_env l ⊢ σR l →*{tr} Some σ ->
    wf_stage_state l σ.
  Proof.
    intros l tr σ Hstep.
    remember (Some σ) as τ; generalize dependent σ.
    induction Hstep; intros σ Hτ; subst.
    * inversion Hτ; subst.
      apply σR_wf.
    * eapply step_wf_state_lemma; eauto.
    * eapply step_wf_state_eps; eauto.
  Qed.

  Lemma step_wf_state_stable : forall l tr σ,
    latch_stage_with_env l ⊢ σR l →*{tr} Some σ ->
    wf_stage_state_stable l σ.
  Proof.
    intros l tr σ Hstep.
    remember (Some σ) as τ; generalize dependent σ.
    induction Hstep; intros σ Hτ; subst.
    * inversion Hτ; subst.
      apply σR_wf_stable.
    * admit (*eapply step_wf_stable_lemma; eauto.
      eapply step_wf_state; eauto.*).
    * eapply step_wf_stable_eps; eauto.
      eapply step_wf_state; eauto.
  Admitted.
    

End WFStage.
