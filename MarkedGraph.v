Require Export Base.

Require Import Omega.

(** * Marked graphs *)
Section MarkedGraphs.

  Variable transition : Set.
  Context `{Htransition : eq_dec transition}.

  Record marked_graph :=
  { place : transition -> transition -> Set
  ; init_marking : forall t1 t2, place t1 t2 -> nat
  }.

  Definition marking (M : marked_graph) := forall t1 t2, place M t1 t2 -> nat.

  Definition is_enabled (M : marked_graph)
                        (t : transition)
                        (m : marking M) :=
    forall (t0 : transition) (p : place M t0 t), 0 < m _ _ p.

  (** A transition should only fire if the caller has independently checked that it
  is enabled. *) 
  Definition fire (t : transition) 
                  (M : marked_graph)
                  (m : marking M)
                : marking M :=
    fun tin tout p =>
        if tin =? tout
        then m _ _ p (* corner case *)
        else if t =? tout (* i.e. if p occurs before t *)
        then m _ _ p - 1
        else if t =? tin (* i.e. if p occurs after t *)
        then m _ _ p + 1
        else m _ _ p.

  (** Reachability *)
  Reserved Notation "{ MG }⊢ t ↓ m" (no associativity, at level 90). 
  Inductive mg_reachable (M : marked_graph)
                        : tail_list transition -> marking M -> Prop :=
  | mg_empty : {M}⊢ t_empty ↓ init_marking M
  | mg_cons : forall e m m' t',
    is_enabled M e m ->
    fire e M m = m' ->
    {M}⊢ t' ↓ m ->
    {M}⊢ t' ▶ e ↓ m'
  where
    "{ MG }⊢ t ↓ m'" := (mg_reachable MG t m').


  (** * Loop lemmas *)
  Inductive mg_path (M : marked_graph) : transition -> transition -> Set :=
  | mg_single_path t1 t2 : place M t1 t2 -> mg_path M t1 t2
  | mg_step_path t1 t2 t3 : place M t1 t2 -> mg_path M t2 t3 -> mg_path M t1 t3
  .
  Arguments mg_single_path {M t1 t2}.
  Arguments mg_step_path {M t1 t2 t3}.
  Definition mg_loop (M : marked_graph) (t : transition) := mg_path M t t.

  (** Add up the markings on each leg of the path *)
  Fixpoint path_cost {M} {t1 t2} (m : marking M) (p : mg_path M t1 t2) : nat :=
    match p with
    | mg_single_path p => m _ _ p
    | mg_step_path p p' => m _ _ p + path_cost m p'
    end.


  Lemma path_cost_single : forall {M : marked_graph} {t1 t2}
        (p : place M t1 t2) (m : marking M),
      m _ _ p = path_cost m (mg_single_path p).
  Proof. intros. reflexivity. Qed.

  Fixpoint path_append {M} {t1 t2} (p1 : mg_path M t1 t2)
    : forall {t3}, mg_path M t2 t3 -> mg_path M t1 t3 :=
    match p1 with
    | mg_single_path p1 => fun _ p2 => mg_step_path p1 p2
    | mg_step_path p1 p2 => fun _ p3 => mg_step_path p1 (path_append p2 p3)
    end.
  

  Lemma path_cost_step : forall {M : marked_graph} {t1 t2 t3}
        (p1 : mg_path M t1 t2) (p2 : mg_path M t2 t3) (m : marking M),
    path_cost m p1 + path_cost m p2 = path_cost m (path_append p1 p2).
  Proof.
    induction p1; intros p2 m.
    + simpl. auto.
    + simpl. rewrite <- IHp1. omega.
  Qed.


  Lemma path_cost_enabled : forall M t m,
    is_enabled M t m ->
    forall t0 (p : mg_path M t0 t),
    path_cost m p > 0.
  Proof.
    intros M t m Henabled t0 p.
    induction p; auto.
    * simpl. apply Henabled.
    * simpl.
      specialize (IHp Henabled).
      omega.
  Qed.

  Ltac specialize_and_rewrite_IH :=
    repeat match goal with
    | [ H : ?x, IH : ?x -> ?z |- _ ] => specialize (IH H)
    | [ IH : ?x = ?x -> ?z |- _ ] => specialize (IH eq_refl)
    | [ IH : ?x = ?y |- context[?x] ] => rewrite IH
    end.

  Lemma fire_preserves_paths : forall M t m, is_enabled M t m ->
     forall t1 t2 (p : mg_path M t1 t2),
     (t <> t1 -> t <> t2 -> path_cost (fire t M m) p = path_cost m p)
  /\ (t = t1  -> t <> t2 -> path_cost (fire t M m) p = path_cost m p + 1)
  /\ (t = t2  -> t <> t1 -> path_cost (fire t M m) p = path_cost m p - 1)
  /\ (t = t1  -> t = t2  -> path_cost (fire t M m) p = path_cost m p).
  Proof.
    intros M t m Henabled t1 t2 p;
    induction p;
      repeat split; intros;
      try (destruct IHp as [IH1 [IH2 [IH3 IH4]]]);
      simpl; unfold fire at 1; subst; reduce_eqb;
        try reflexivity;
        specialize_and_rewrite_IH.
    * compare_next; auto.
    * repeat compare_next; specialize_and_rewrite_IH; auto.
      specialize (Henabled _ p).
      omega.
    * compare_next; specialize_and_rewrite_IH; auto; try omega.
    * assert (path_cost m p0 > 0). { apply path_cost_enabled; auto. }
      repeat compare_next; specialize_and_rewrite_IH; auto; try omega.
      assert (m t1 t2 p > 0). { apply Henabled. }
      omega.
    * repeat compare_next; specialize_and_rewrite_IH; auto; try omega.
      assert (path_cost m p0 > 0). { apply path_cost_enabled; auto. }
      omega.
  Qed.

  (** Main loop lemma *)
  Lemma mg_preserves_loops : forall M ts m,
    {M}⊢ ts ↓ m ->
    forall t (p : mg_loop M t),
      path_cost m p = path_cost (init_marking M) p.
  Proof.
    intros M ts m Hm.
    induction Hm as [ | e m m' ts' Henabled Hfire Hm];
      intros t p.
    * reflexivity.
    * subst.

      set (H := fire_preserves_paths M e m Henabled _ _ p).
      destruct H as [Hneq [_ [_ Heq]]].

      compare e t.
      { rewrite Heq; auto. }
      { rewrite Hneq; auto. }
  Qed.


End MarkedGraphs.

Arguments mg_reachable {transition Htransition} M.
Notation "{ MG }⊢ s ↓ m" := (mg_reachable MG s m) (no associativity, at level 90).


Arguments place {transition}.
Arguments init_marking {transition}.
Arguments is_enabled {transition}.
Arguments fire {transition place} t M {Hinput Houtput} : rename.
Arguments marking {transition}.

Ltac solve_loop :=
  repeat rewrite path_cost_single;
  repeat rewrite path_cost_step;
  match goal with
  [ H : { ?M }⊢ _ ↓ _ |- _ ] => rewrite (@mg_preserves_loops _ _ M _ _ H) 
  end;
  simpl.


