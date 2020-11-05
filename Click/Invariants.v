Require Import Base.
Require Import Circuit.
Require Import StateSpace.
Require Import Click.StateSpace.
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



  (***************************************************************************
   * Identify invariants that hold of all states reachable by a Click stage
   * from σR
   *
  ****************************************************************************)

  Record wf_stage_state (l : latch even odd) (σ : state name) : Prop :=
    { wf_all_bits : forall x, x ∈ space_domain (latch_stage_with_env l) -> val_is_bit (σ x)
    ; wf_ctrl_reset_n : σ ctrl_reset_n = Bit1
    ; wf_dp_reset_n : σ dp_reset_n = Bit1
    ; wf_hidden : σ (latch_hidden l) = Bit1

    ; wf_clk_unstable : σ (latch_state0 l) = σ (latch_not_state0 l) ->
                        σ (latch_clk l) = σ (latch_old_clk l)
    }.
  Record wf_stage_state_stable  (l : latch even odd) (σ : state name) : Prop :=
    { wf_left_ack_stable  : ~ stable (latch_left_ack_component l) σ ->
                              stable (latch_flop_component l) σ

    ; wf_right_req_stable : ~ stable (latch_right_req_component l) σ ->
                              stable (latch_flop_component l) σ

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
                let Hunstable := fresh "Hunstable" in
                destruct Hstep as [Hequiv Heq];
                simpl in Heq;
                try match type of Heq with
                | ?x = ?x -> _ => specialize (Heq eq_refl); destruct Heq as [Heq Hunstable]
(*                | ?x = ?y -> _ => clear Heq (* too much?? *)*)
                end
    end
  end.


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
    { intros Heq. Print wf_stage_state.
      apply wf_clk_unstable in Heq; auto.
    }

    { (* clk = 1 *)

      set (Hhidden := wf_hidden l σ Hwf).
      set (Hreset := wf_dp_reset_n l σ Hwf).
      simpl in Hhidden, Hreset.

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
            { apply Hwf.
              rewrite dom_latch_stage_with_env. solve_space_set.
            }
          }
          { reflexivity. }
          { intros x Hx. reflexivity. }
      }
      { apply Flop_input; [ | solve_space_set; destruct l; auto | intros ? ?; auto].
        left.
        set (Hhidden := wf_hidden l σ Hwf).
        set (Hreset := wf_dp_reset_n l σ Hwf).

        destruct l; simpl; auto;
        simpl in Hhidden, Hreset; rewrite Hreset, Hhidden; simpl;
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


  Lemma latch_flop_component_stable : forall l σ,
    wf_stage_state l σ ->
    stable (latch_flop_component l) σ <->
    (σ (latch_clk l) = σ (latch_old_clk l) /\ σ (latch_state0 l) = neg_value (σ (latch_not_state0 l))).
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
                           :: latch_clk l ::nil)).
        { apply wf_space in Hstep; auto. 
          destruct l; simpl in Hstep; decompose_set_structure; solve_space_set.
        }
        decompose_set_structure.
        ++ repeat step_inversion_1.
           constructor. destruct l; simpl; solve_set.
        ++ repeat step_inversion_1.
           apply flop_inversion_output in Hstep1.
           2:{ solve_all_disjoint. }
           2:{ destruct l; simpl; destruct Hwf; auto. }
           2:{ destruct l; simpl; destruct Hwf; auto. }

           contradict Hclk.
           destruct Hstep1 as [Hclk1 [Hclk2 _]].
           rewrite Hclk1. auto.
        ++ constructor. simpl. solve_set.

      + do 3 step_inversion_1.
        ++ repeat step_inversion_1.
           { inversion Hstep; subst; auto. find_contradiction. }
        ++ step_inversion_1.
           assert (Hstable : stable (func_space nil (latch_hidden l) (fun _ => Num 1)) σ).
           { apply func_stable_equiv.
             { solve_set. }
             { destruct Hwf; auto. }
           }
           (* Contradiction *)
           destruct Hstable as [_ Hstable].
           specialize (Hstable _ _ Hstep2).
           inversion Hstable; subst.
           contradict pf.
        ++ do 2 step_inversion_1.
           assert (Hstable : stable (NOT (latch_state0 l) (latch_not_state0 l)) σ).
           { (* from Hstate0 *)
             apply func_stable_equiv; auto.
             { solve_space_set. }
             { rewrite Hstate0.
               rewrite val_is_bit_neg_neg; auto.
               apply Hwf. rewrite dom_latch_stage_with_env. solve_space_set. }
           }
           destruct Hstable as [_ Hstable].
           specialize (Hstable _ _ Hstep2).
           inversion Hstable; subst.
           contradict pf.
           simpl. solve_space_set.
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
    assert (Hclk : σR l (latch_state0 l) = σR l (latch_not_state0 l) ->
                   σR l (latch_clk l) = σR l (latch_old_clk l)).
    { unfold σR. simpl. reduce_eqb. }

    split; auto.
  Qed.
  Lemma σR_wf_stable : forall l,
    wf_stage_state_stable l (σR l).
  Proof.
    split.
    { intros Hstable. apply latch_flop_component_stable.
      { apply σR_wf. }
      split; unfold σR; simpl; reduce_eqb; auto.
    }
    { intros Hstable. apply latch_flop_component_stable.
      { apply σR_wf. }
      split; unfold σR; simpl; reduce_eqb; auto.
    }
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
      combine_state_equiv_on_complex; auto.
      { destruct l; solve_space_set. }
      standardize_state_equiv_on_set Hequiv.

      match type of Hequiv with
      | state_equiv_on ?X _ _ =>
        assert (HX : X == space_domain (latch_stage_with_env l))
      end.
      { rewrite dom_latch_stage_with_env.
        split; intros z Hz; to_in_list_dec; simpl in Hz;    
          repeat (compare_next; auto); destruct l; simpl; reduce_eqb; auto.
      }
      rewrite HX in *; clear HX.

      constructor.
      + (* val_is_bit *)
        intros y HY.
        rewrite_state_equiv; auto.
        repeat compare_next; auto.
        solve_val_is_bit.

      + (* ctrl_reset_n *)
        rewrite_state_equiv; auto.
        { rewrite dom_latch_stage_with_env. solve_space_set. }

      + (* dp_reset_n *)
        rewrite_state_equiv; auto.
        { rewrite dom_latch_stage_with_env; solve_space_set. }

      + (* latch_hidden *)
        rewrite_state_equiv; auto.
        { rewrite dom_latch_stage_with_env; solve_space_set. }

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

      combine_state_equiv_on_complex.
      { destruct l; solve_space_set. }

      standardize_state_equiv_on_set Hequiv.
      match goal with
      | [ Hequiv : state_equiv_on ?X _ _ |- _ ] =>
        assert (HX : X == space_domain (latch_stage_with_env l))
      end.
      { rewrite dom_latch_stage_with_env. clear Hequiv.
        split; intros z Hz; to_in_list_dec;
          simpl in Hz;
          repeat (compare_next; auto);
          simpl; reduce_eqb; auto;
          destruct l; simpl; reduce_eqb; auto.
      }
      rewrite HX in Hequiv. clear HX.

      assert (H_val_is_bit : forall x0 : name, x0 ∈ space_domain (latch_stage_with_env l) ->
                             val_is_bit (σ' x0)).
      {
        intros y HY.
        rewrite_state_equiv; auto.
        compare_next; auto.
        assert (Hstate0 : val_is_bit (σ (latch_state0 l))) by solve_val_is_bit.
        destruct l; simpl; auto. inversion Hstate0; constructor.
      }
      constructor.

      + (* val_is_bit *) auto.
      + (* ctrl_reset_n *)
        rewrite_state_equiv; auto.
        rewrite dom_latch_stage_with_env. solve_space_set.
      + (* dp_reset_n *)
        rewrite_state_equiv; auto.
        rewrite dom_latch_stage_with_env. solve_space_set.
      + (* latch_hidden *)
        rewrite_state_equiv; auto.
        rewrite dom_latch_stage_with_env. solve_space_set.

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

Lemma step_wf_stable_lemma : forall l σ e σ',
    wf_stage_state l σ ->
    wf_stage_state_stable l σ ->
    latch_stage_with_env l ⊢ σ →{Some e} Some σ' ->
    wf_stage_state_stable l σ'.
Admitted.


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

  Lemma step_wf_state_eps : forall l σ σ',
    wf_stage_state l σ ->
    latch_stage_with_env l ⊢ σ →{None} Some σ' ->
    wf_stage_state l σ'.
  Proof.
    intros l σ σ' [Hwf1 Hwf2 Hwf3 Hwf4] Hstep.
    set (Hdisjoint := scheme_all_disjoint l).

    repeat step_inversion_1; repeat combine_state_equiv_on.
    * standardize_state_equiv_on_set Hequiv0.
      inversion Hstep; subst.
      standardize_state_equiv_on_set H2.
      combine_state_equiv_on_complex.
      { simpl. solve_space_set. }
      standardize_state_equiv_on_set Hequiv.
      assert (Hequiv' : state_equiv_on (space_domain (latch_stage_with_env l))
                          (Some (update σ (latch_old_clk l) (σ (latch_clk l))))
                          (Some σ')).
      { intros x Hx. apply Hequiv.
        clear Hequiv.
        rewrite dom_latch_stage_with_env in Hx.
        simpl in Hx. decompose_set_structure;
          solve_in_dom.
      }
      clear Hequiv.
      
      assert (Hold : σ' (latch_old_clk l) = σ (latch_clk l)).
      { rewrite_state_equiv.
        2:{ solve_in_dom. }
        reduce_eqb; auto.
      }
      constructor.
      + intros x Hx.
        compare x (latch_old_clk l).
        { (* eq *) rewrite Hold.
          apply Hwf1. solve_in_dom.
        }
        { (* <> *)
          rewrite <- Hequiv'; auto.
          { unfold update. reduce_eqb. solve_val_is_bit. }
        }
      + rewrite_state_equiv; auto; solve_in_dom.
      + rewrite_state_equiv; auto; solve_in_dom.
      + rewrite_state_equiv; auto; solve_in_dom.
      + rewrite <- Hequiv'; [ | solve_in_dom ].
        rewrite <- Hequiv'; [ | solve_in_dom ].
        rewrite <- Hequiv'; [ | solve_in_dom ].
        rewrite <- Hequiv'; [ | solve_in_dom ].
        unfold update; simpl. reduce_eqb. auto.

    * standardize_state_equiv_on_set Hequiv1.
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
    * eapply step_wf_stable_lemma; eauto.
      eapply step_wf_state; eauto.
    * eapply step_wf_stable_eps; eauto.
      eapply step_wf_state; eauto.
  Qed.
    

End WFStage.
