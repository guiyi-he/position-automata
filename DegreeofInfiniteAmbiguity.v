From Stdlib Require Import List Bool Arith Lia.
Import ListNotations.

From PositionAutomata Require Import DegreeofAmbiguity GraphAlgorithms.

(** Weber-Seidl style ambiguity witnesses.

    This file intentionally starts with the ReDoS-relevant, executable core:
    fuel-bounded search procedures for IDA and EDA witnesses, together with
    soundness theorems into the Prop-level criteria.  The complete converse
    directions from Weber and Seidl Section 3/4 are left as future theorem
    targets rather than assumed as axioms. *)

Section InfiniteAmbiguity.
  Context {A : Type}.

  Definition finite_state (m : @finite_nfa A) : Type :=
    nfa_state (fnfa_base m).

  Definition finite_delta_star
      (m : @finite_nfa A)
      (p : finite_state m)
      (w : list A)
      (q : finite_state m) : Prop :=
    path_from (fnfa_base m) p w q.

  Definition finite_useful
      (m : @finite_nfa A)
      (q : finite_state m) : Prop :=
    useful_state (fnfa_base m) q.

  Definition IDA (m : @finite_nfa A) : Prop :=
    exists p q v,
      p <> q /\
      finite_useful m p /\
      finite_useful m q /\
      finite_delta_star m p v p /\
      finite_delta_star m p v q /\
      finite_delta_star m q v q.

  Definition EDA (m : @finite_nfa A) : Prop :=
    exists q v,
      finite_useful m q /\
      finite_delta_star m q v q /\
      2 <= da_from_to m q v q.

  Definition finite_layer (m : @finite_nfa A) : Type :=
    ((finite_state m * finite_state m) * list A)%type.

  Definition layer_left
      (m : @finite_nfa A)
      (l : finite_layer m) : finite_state m :=
    fst (fst l).

  Definition layer_right
      (m : @finite_nfa A)
      (l : finite_layer m) : finite_state m :=
    snd (fst l).

  Definition layer_word
      (m : @finite_nfa A)
      (l : finite_layer m) : list A :=
    snd l.

  Definition IDA_layer (m : @finite_nfa A) (l : finite_layer m) : Prop :=
    let r := layer_left m l in
    let s := layer_right m l in
    let v := layer_word m l in
    r <> s /\
    finite_useful m r /\
    finite_useful m s /\
    finite_delta_star m r v r /\
    finite_delta_star m r v s /\
    finite_delta_star m s v s.

  Fixpoint IDA_layer_connectors
      (m : @finite_nfa A)
      (layers : list (finite_layer m))
      (connectors : list (list A)) : Prop :=
    match layers, connectors with
    | [], [] => True
    | [_], [] => True
    | l1 :: l2 :: rest, u :: us =>
        finite_delta_star m (layer_right m l1) u (layer_left m l2) /\
        IDA_layer_connectors m (l2 :: rest) us
    | _, _ => False
    end.

  Definition IDA_d (m : @finite_nfa A) (d : nat) : Prop :=
    exists layers connectors,
      length layers = d /\
      length connectors = pred d /\
      Forall (IDA_layer m) layers /\
      IDA_layer_connectors m layers connectors.

  Definition has_exponential_pump := EDA.

  Definition exponential_ambiguity_lower_bound (m : @nfa A) : Prop :=
    exists prefix pump suffix,
      forall n,
        Nat.pow 2 n <=
        ambiguity_of_word m (prefix ++ word_power pump n ++ suffix).

  Fixpoint words_upto (alphabet : list A) (fuel : nat) : list (list A) :=
    match fuel with
    | O => [[]]
    | S fuel' =>
        words_upto alphabet fuel' ++ words_of_length alphabet (S fuel')
    end.

  Definition pathb
      (m : @finite_nfa A)
      (p : finite_state m)
      (w : list A)
      (q : finite_state m) : bool :=
    0 <? da_from_to m p w q.

  Definition usefulb_with_fuel
      (fuel : nat)
      (m : @finite_nfa A)
      (q : finite_state m) : bool :=
    existsb
      (fun w => 0 <? start_runs_to m w q)
      (words_upto (fnfa_alphabet m) fuel)
    &&
    existsb
      (fun w => 0 <? accepting_runs_from (fnfa_base m) q w)
      (words_upto (fnfa_alphabet m) fuel).

  Definition eda_stateb
      (fuel : nat)
      (m : @finite_nfa A)
      (q : finite_state m) : bool :=
    usefulb_with_fuel fuel m q
    &&
    existsb
      (fun v => 1 <? da_from_to m q v q)
      (words_upto (fnfa_alphabet m) fuel).

  Definition edab_with_fuel (fuel : nat) (m : @finite_nfa A) : bool :=
    existsb (eda_stateb fuel m) (fnfa_states m).

  Definition idab_pairb
      (fuel : nat)
      (m : @finite_nfa A)
      (p q : finite_state m) : bool :=
    negb (fnfa_state_eqb m p q)
    &&
    usefulb_with_fuel fuel m p
    &&
    usefulb_with_fuel fuel m q
    &&
    existsb
      (fun v =>
         pathb m p v p && pathb m p v q && pathb m q v q)
      (words_upto (fnfa_alphabet m) fuel).

  Definition idab_with_fuel (fuel : nat) (m : @finite_nfa A) : bool :=
    existsb
      (fun p => existsb (idab_pairb fuel m p) (fnfa_states m))
      (fnfa_states m).

  Fixpoint lists_of_length {B : Type} (xs : list B) (n : nat)
      : list (list B) :=
    match n with
    | O => [[]]
    | S n' =>
        concat
          (map
             (fun x => map (fun ys => x :: ys) (lists_of_length xs n'))
             xs)
    end.

  Definition ida_layer_choices
      (fuel : nat)
      (m : @finite_nfa A) : list (finite_layer m) :=
    let words := words_upto (fnfa_alphabet m) fuel in
    concat
      (map
         (fun r =>
            concat
              (map
                 (fun s => map (fun v => ((r, s), v)) words)
                 (fnfa_states m)))
         (fnfa_states m)).

  Definition ida_layerb
      (fuel : nat)
      (m : @finite_nfa A)
      (l : finite_layer m) : bool :=
    let r := layer_left m l in
    let s := layer_right m l in
    let v := layer_word m l in
    negb (fnfa_state_eqb m r s)
    &&
    (usefulb_with_fuel fuel m r
     &&
     (usefulb_with_fuel fuel m s
      &&
      (pathb m r v r
       &&
       (pathb m r v s && pathb m s v s)))).

  Fixpoint ida_layersb
      (fuel : nat)
      (m : @finite_nfa A)
      (layers : list (finite_layer m)) : bool :=
    match layers with
    | [] => true
    | l :: layers' => ida_layerb fuel m l && ida_layersb fuel m layers'
    end.

  Fixpoint ida_connectorsb
      (m : @finite_nfa A)
      (layers : list (finite_layer m))
      (connectors : list (list A)) : bool :=
    match layers, connectors with
    | [], [] => true
    | [_], [] => true
    | l1 :: l2 :: rest, u :: us =>
        pathb m (layer_right m l1) u (layer_left m l2)
        &&
        ida_connectorsb m (l2 :: rest) us
    | _, _ => false
    end.

  Definition idadb_with_fuel
      (fuel d : nat)
      (m : @finite_nfa A) : bool :=
    let layers := lists_of_length (ida_layer_choices fuel m) d in
    let connectors :=
      lists_of_length (words_upto (fnfa_alphabet m) fuel) (pred d) in
    existsb
      (fun ls =>
         existsb
           (fun us => ida_layersb fuel m ls && ida_connectorsb m ls us)
          connectors)
      layers.

  Definition state_inb
      (m : @finite_nfa A)
      (q : finite_state m) : bool :=
    existsb (fnfa_state_eqb m q) (fnfa_states m).

  Definition step_to_stateb
      (m : @finite_nfa A)
      (q : finite_state m)
      (a : A)
      (q' : finite_state m) : bool :=
    existsb (fnfa_state_eqb m q') (nfa_step (fnfa_base m) q a).

  Definition transitionb
      (m : @finite_nfa A)
      (q q' : finite_state m) : bool :=
    existsb
      (fun a => step_to_stateb m q a q')
      (fnfa_alphabet m).

  Definition state_reachb
      (m : @finite_nfa A)
      (p q : finite_state m) : bool :=
    reachb
      (fnfa_state_eqb m)
      (fnfa_states m)
      (transitionb m)
      (length (fnfa_states m))
      p q.

  Definition state_connectedb
      (m : @finite_nfa A)
      (p q : finite_state m) : bool :=
    connectedb
      (fnfa_state_eqb m)
      (fnfa_states m)
      (transitionb m)
      (length (fnfa_states m))
      p q.

  Definition usefulb_graph
      (m : @finite_nfa A)
      (q : finite_state m) : bool :=
    existsb
      (fun q0 => state_reachb m q0 q)
      (nfa_start (fnfa_base m))
    &&
    existsb
      (fun qf => nfa_final (fnfa_base m) qf && state_reachb m q qf)
      (fnfa_states m).

  Definition state_pair (m : @finite_nfa A) : Type :=
    (finite_state m * finite_state m)%type.

  Definition state_pair_vertices (m : @finite_nfa A) : list (state_pair m) :=
    list_prod (fnfa_states m) (fnfa_states m).

  Definition state_pair_eqb
      (m : @finite_nfa A)
      (x y : state_pair m) : bool :=
    fnfa_state_eqb m (fst x) (fst y)
    && fnfa_state_eqb m (snd x) (snd y).

  Definition g2_edgeb
      (m : @finite_nfa A)
      (x y : state_pair m) : bool :=
    existsb
      (fun a =>
         step_to_stateb m (fst x) a (fst y)
         && step_to_stateb m (snd x) a (snd y))
      (fnfa_alphabet m).

  Definition g2_reachb
      (m : @finite_nfa A)
      (x y : state_pair m) : bool :=
    reachb
      (state_pair_eqb m)
      (state_pair_vertices m)
      (g2_edgeb m)
      (length (state_pair_vertices m))
      x y.

  Definition g2_connectedb
      (m : @finite_nfa A)
      (x y : state_pair m) : bool :=
    connectedb
      (state_pair_eqb m)
      (state_pair_vertices m)
      (g2_edgeb m)
      (length (state_pair_vertices m))
      x y.

  Definition edab_graph (m : @finite_nfa A) : bool :=
    existsb
      (fun q =>
         usefulb_graph m q
         &&
         existsb
           (fun pr =>
              negb (fnfa_state_eqb m (fst pr) (snd pr))
              && g2_connectedb m (q, q) pr)
           (state_pair_vertices m))
      (fnfa_states m).

  Definition state_triple (m : @finite_nfa A) : Type :=
    ((finite_state m * finite_state m) * finite_state m)%type.

  Definition triple_first
      (m : @finite_nfa A)
      (x : state_triple m) : finite_state m :=
    fst (fst x).

  Definition triple_second
      (m : @finite_nfa A)
      (x : state_triple m) : finite_state m :=
    snd (fst x).

  Definition triple_third
      (m : @finite_nfa A)
      (x : state_triple m) : finite_state m :=
    snd x.

  Definition state_triple_vertices
      (m : @finite_nfa A) : list (state_triple m) :=
    concat
      (map
         (fun p =>
            concat
              (map
                 (fun q => map (fun r => ((p, q), r)) (fnfa_states m))
                 (fnfa_states m)))
         (fnfa_states m)).

  Definition state_triple_eqb
      (m : @finite_nfa A)
      (x y : state_triple m) : bool :=
    (fnfa_state_eqb m (triple_first m x) (triple_first m y)
     &&
     fnfa_state_eqb m (triple_second m x) (triple_second m y))
    && fnfa_state_eqb m (triple_third m x) (triple_third m y).

  Definition g3_edgeb
      (m : @finite_nfa A)
      (x y : state_triple m) : bool :=
    existsb
      (fun a =>
         step_to_stateb m (triple_first m x) a (triple_first m y)
         &&
         step_to_stateb m (triple_second m x) a (triple_second m y)
         &&
         step_to_stateb m (triple_third m x) a (triple_third m y))
      (fnfa_alphabet m).

  Definition g3_reachb
      (m : @finite_nfa A)
      (x y : state_triple m) : bool :=
    reachb
      (state_triple_eqb m)
      (state_triple_vertices m)
      (g3_edgeb m)
      (length (state_triple_vertices m))
      x y.

  Definition idab_graph (m : @finite_nfa A) : bool :=
    existsb
      (fun p =>
         existsb
           (fun q =>
              negb (fnfa_state_eqb m p q)
              &&
              usefulb_graph m p
              &&
              usefulb_graph m q
              &&
              g3_reachb m ((p, p), q) ((p, q), q))
           (fnfa_states m))
      (fnfa_states m).

  Definition g5_redgeb
      (m : @finite_nfa A)
      (ci cj : finite_state m) : bool :=
    existsb
      (fun p =>
         state_connectedb m ci p
         &&
         usefulb_graph m p
         &&
         existsb
           (fun q =>
              state_connectedb m cj q
              &&
              usefulb_graph m q
              &&
              negb (fnfa_state_eqb m p q)
              &&
              g3_reachb m ((p, p), q) ((p, q), q))
           (fnfa_states m))
      (fnfa_states m).

  Definition g5_edgeb
      (m : @finite_nfa A)
      (ci cj : finite_state m) : bool :=
    g5_redgeb m ci cj || state_reachb m ci cj.

  Definition g5_degree_lower_boundb (m : @finite_nfa A) : nat :=
    max_special_edges
      (fnfa_states m)
      (g5_edgeb m)
      (g5_redgeb m)
      (length (fnfa_states m)).

  Definition ida_degree_lower_boundb (m : @finite_nfa A) : nat :=
    g5_degree_lower_boundb m.

  Definition ida_db_graph (d : nat) (m : @finite_nfa A) : bool :=
    d <=? ida_degree_lower_boundb m.

  Inductive ambiguity_growth : Type :=
  | FiniteAmbiguity : ambiguity_growth
  | PolynomialAmbiguity : nat -> ambiguity_growth
  | ExponentialAmbiguity : ambiguity_growth.

  Definition ambiguity_growth_eqb
      (x y : ambiguity_growth) : bool :=
    match x, y with
    | FiniteAmbiguity, FiniteAmbiguity => true
    | PolynomialAmbiguity d, PolynomialAmbiguity e => Nat.eqb d e
    | ExponentialAmbiguity, ExponentialAmbiguity => true
    | _, _ => false
    end.

  Definition degree_growthb (m : @finite_nfa A) : ambiguity_growth :=
    if edab_graph m then ExponentialAmbiguity
    else
      match ida_degree_lower_boundb m with
      | O => FiniteAmbiguity
      | S d => PolynomialAmbiguity (S d)
      end.

  Lemma pathb_sound :
    forall (m : @finite_nfa A) p w q,
      pathb m p w q = true ->
      finite_delta_star m p w q.
  Proof.
    intros m p w q H.
    unfold pathb in H.
    apply Nat.ltb_lt in H.
    now apply runs_between_positive_path.
  Qed.

  Lemma usefulb_with_fuel_sound :
    forall fuel (m : @finite_nfa A) q,
      usefulb_with_fuel fuel m q = true ->
      finite_useful m q.
  Proof.
    intros fuel m q H.
    unfold usefulb_with_fuel in H.
    apply andb_true_iff in H as [Hin Hout].
    apply existsb_exists in Hin as [w_in [_ Hin]].
    apply existsb_exists in Hout as [w_out [_ Hout]].
    apply Nat.ltb_lt in Hin.
    apply Nat.ltb_lt in Hout.
    eapply useful_state_from_positive_tests; eauto.
  Qed.

  Lemma eda_stateb_sound :
    forall fuel (m : @finite_nfa A) q,
      eda_stateb fuel m q = true ->
      exists v,
        finite_useful m q /\
        finite_delta_star m q v q /\
        2 <= da_from_to m q v q.
  Proof.
    intros fuel m q H.
    unfold eda_stateb in H.
    apply andb_true_iff in H as [Huseful Hloop].
    apply existsb_exists in Hloop as [v [_ Hv]].
    apply Nat.ltb_lt in Hv.
    exists v.
    repeat split.
    - now apply usefulb_with_fuel_sound with (fuel := fuel).
    - unfold da_from_to in Hv.
      apply runs_between_positive_path. lia.
    - lia.
  Qed.

  Theorem edab_with_fuel_sound :
    forall fuel (m : @finite_nfa A),
      edab_with_fuel fuel m = true ->
      EDA m.
  Proof.
    intros fuel m H.
    unfold edab_with_fuel in H.
    apply existsb_exists in H as [q [_ Hq]].
    destruct (eda_stateb_sound fuel m q Hq) as [v [Huseful [Hloop Hcount]]].
    exists q, v.
    repeat split; assumption.
  Qed.

  Theorem edab_with_fuel_has_exponential_pump :
    forall fuel (m : @finite_nfa A),
      edab_with_fuel fuel m = true ->
      has_exponential_pump m.
  Proof.
    intros fuel m H.
    now apply edab_with_fuel_sound in H.
  Qed.

  Lemma idab_pairb_sound :
    forall fuel (m : @finite_nfa A) p q,
      idab_pairb fuel m p q = true ->
      exists v,
        p <> q /\
        finite_useful m p /\
        finite_useful m q /\
        finite_delta_star m p v p /\
        finite_delta_star m p v q /\
        finite_delta_star m q v q.
  Proof.
    intros fuel m p q H.
    unfold idab_pairb in H.
    apply andb_true_iff in H as [Hleft Hv].
    apply andb_true_iff in Hleft as [Hleft Huseful_q].
    apply andb_true_iff in Hleft as [Hneq Huseful_p].
    apply existsb_exists in Hv as [v [_ Hv]].
    apply andb_true_iff in Hv as [Hleft Hqq].
    apply andb_true_iff in Hleft as [Hpp Hpq].
    exists v.
    repeat split.
    - intros Heq. subst.
      pose proof (fnfa_state_eqb_complete m q q eq_refl) as Hrefl.
      rewrite Hrefl in Hneq. discriminate.
    - now apply usefulb_with_fuel_sound with (fuel := fuel).
    - now apply usefulb_with_fuel_sound with (fuel := fuel).
    - now apply pathb_sound.
    - now apply pathb_sound.
    - now apply pathb_sound.
  Qed.

  Theorem idab_with_fuel_sound :
    forall fuel (m : @finite_nfa A),
      idab_with_fuel fuel m = true ->
      IDA m.
  Proof.
    intros fuel m H.
    unfold idab_with_fuel in H.
    apply existsb_exists in H as [p [_ Hp]].
    apply existsb_exists in Hp as [q [_ Hq]].
    destruct (idab_pairb_sound fuel m p q Hq)
      as [v [Hneq [Hup [Huq [Hpp [Hpq Hqq]]]]]].
    exists p, q, v.
    repeat split; assumption.
  Qed.

  Lemma state_inb_sound :
    forall (m : @finite_nfa A) q,
      state_inb m q = true ->
      In q (fnfa_states m).
  Proof.
    intros m q H.
    unfold state_inb in H.
    apply existsb_exists in H as [q' [Hin Heq]].
    apply fnfa_state_eqb_sound in Heq.
    now subst.
  Qed.

  Lemma step_to_stateb_sound :
    forall (m : @finite_nfa A) q a q',
      step_to_stateb m q a q' = true ->
      In q' (nfa_step (fnfa_base m) q a).
  Proof.
    intros m q a q' H.
    unfold step_to_stateb in H.
    apply existsb_exists in H as [r [Hin Heq]].
    apply fnfa_state_eqb_sound in Heq.
    now subst.
  Qed.

  Lemma transitionb_sound :
    forall (m : @finite_nfa A) q q',
      transitionb m q q' = true ->
      exists a,
        In a (fnfa_alphabet m) /\
        In q' (nfa_step (fnfa_base m) q a).
  Proof.
    intros m q q' H.
    unfold transitionb in H.
    apply existsb_exists in H as [a [Ha Hstep]].
    exists a. split; auto.
    now apply step_to_stateb_sound in Hstep.
  Qed.

  Lemma transition_walk_path :
    forall (m : @finite_nfa A) p q,
      walk (transitionb m) p q ->
      exists w, finite_delta_star m p w q.
  Proof.
    intros m p q Hwalk.
    induction Hwalk as [x| x y z Hedge _ [w Hw]].
    - exists []. constructor.
    - destruct (transitionb_sound m x y Hedge) as [a [_ Hstep]].
      exists (a :: w).
      eapply Path_cons; eauto.
  Qed.

  Lemma state_reachb_sound_path :
    forall (m : @finite_nfa A) p q,
      state_reachb m p q = true ->
      exists w, finite_delta_star m p w q.
  Proof.
    intros m p q H.
    unfold state_reachb in H.
    pose proof
      (@reachb_sound
         (finite_state m)
         (fnfa_state_eqb m)
         (fnfa_state_eqb_sound m)
         (fnfa_states m)
         (transitionb m)
         (length (fnfa_states m))
         p q H) as Hwalk.
    now apply transition_walk_path.
  Qed.

  Lemma usefulb_graph_sound :
    forall (m : @finite_nfa A) q,
      usefulb_graph m q = true ->
      finite_useful m q.
  Proof.
    intros m q H.
    unfold usefulb_graph in H.
    apply andb_true_iff in H as [Hin Hout].
    apply existsb_exists in Hin as [q0 [Hstart Hreach_in]].
    apply existsb_exists in Hout as [qf [_ Hfinal_reach]].
    apply andb_true_iff in Hfinal_reach as [Hfinal Hreach_out].
    destruct (state_reachb_sound_path m q0 q Hreach_in) as [w_in Hpath_in].
    destruct (state_reachb_sound_path m q qf Hreach_out) as [w_out Hpath_out].
    exists q0, qf, w_in, w_out.
    repeat split; assumption.
  Qed.

  Lemma state_pair_eqb_sound :
    forall (m : @finite_nfa A) (x y : state_pair m),
      state_pair_eqb m x y = true -> x = y.
  Proof.
    intros m [x1 x2] [y1 y2] H.
    unfold state_pair_eqb in H. simpl in H.
    apply andb_true_iff in H as [H1 H2].
    apply fnfa_state_eqb_sound in H1.
    apply fnfa_state_eqb_sound in H2.
    subst. reflexivity.
  Qed.

  Lemma g2_edgeb_sound :
    forall (m : @finite_nfa A) x y,
      g2_edgeb m x y = true ->
      exists a,
        In a (fnfa_alphabet m) /\
        In (fst y) (nfa_step (fnfa_base m) (fst x) a) /\
        In (snd y) (nfa_step (fnfa_base m) (snd x) a).
  Proof.
    intros m x y H.
    unfold g2_edgeb in H.
    apply existsb_exists in H as [a [Ha Hsteps]].
    apply andb_true_iff in Hsteps as [H1 H2].
    exists a. repeat split; auto;
      now apply step_to_stateb_sound.
  Qed.

  Lemma g2_walk_paths :
    forall (m : @finite_nfa A) x y,
      walk (g2_edgeb m) x y ->
      exists w,
        finite_delta_star m (fst x) w (fst y) /\
        finite_delta_star m (snd x) w (snd y).
  Proof.
    intros m x y Hwalk.
    induction Hwalk as [x| x y z Hedge _ [w [Hleft Hright]]].
    - exists []. split; constructor.
    - destruct x as [x1 x2].
      destruct y as [y1 y2].
      destruct z as [z1 z2].
      simpl in *.
      destruct (g2_edgeb_sound m (x1, x2) (y1, y2) Hedge)
        as [a [_ [Hstep1 Hstep2]]].
      exists (a :: w). split; eapply Path_cons; eauto.
  Qed.

  Theorem edab_graph_sound :
    forall (m : @finite_nfa A),
      edab_graph m = true -> EDA m.
  Proof.
    intros m H.
    unfold edab_graph in H.
    apply existsb_exists in H as [q [_ Hq]].
    apply andb_true_iff in Hq as [Huseful Hpair].
    apply usefulb_graph_sound in Huseful.
    apply existsb_exists in Hpair as [[p r] [_ Hpr]].
    apply andb_true_iff in Hpr as [Hneq Hconn].
    apply negb_true_iff in Hneq.
    assert (Hdiff : p <> r).
    {
      intros Heq.
      subst r.
      simpl in Hneq.
      rewrite (fnfa_state_eqb_complete m p p eq_refl) in Hneq.
      discriminate.
    }
    pose proof
      (@connectedb_sound
         (state_pair m)
         (state_pair_eqb m)
         (state_pair_eqb_sound m)
         (state_pair_vertices m)
         (g2_edgeb m)
         (length (state_pair_vertices m))
         (q, q) (p, r) Hconn) as [Hqr Hrq].
    destruct (g2_walk_paths m (q, q) (p, r) Hqr)
      as [u [Hqp Hqr_path]].
    destruct (g2_walk_paths m (p, r) (q, q) Hrq)
      as [v [Hpq Hrq_path]].
    exists q, (u ++ v).
    repeat split.
    - exact Huseful.
    - eapply path_from_app; eauto.
    - pose proof (path_runs_between_positive m q u p Hqp) as Hqp_count.
      pose proof (path_runs_between_positive m q u r Hqr_path) as Hqr_count.
      pose proof (path_runs_between_positive m p v q Hpq) as Hpq_count.
      pose proof (path_runs_between_positive m r v q Hrq_path) as Hrq_count.
      pose proof
        (runs_between_app_lower_two m p r q u v q Hdiff) as Hlower.
      unfold da_from_to in *.
      assert
        (2 <=
         runs_between m q u p * runs_between m p v q +
         runs_between m q u r * runs_between m r v q).
      {
        assert (1 <= runs_between m q u p * runs_between m p v q)
          by (apply Nat.mul_pos_pos; assumption).
        assert (1 <= runs_between m q u r * runs_between m r v q)
          by (apply Nat.mul_pos_pos; assumption).
        lia.
      }
      lia.
  Qed.

  Lemma state_triple_eqb_sound :
    forall (m : @finite_nfa A) (x y : state_triple m),
      state_triple_eqb m x y = true -> x = y.
  Proof.
    intros m [[x1 x2] x3] [[y1 y2] y3] H.
    unfold state_triple_eqb in H. simpl in H.
    apply andb_true_iff in H as [H12 Hthird].
    apply andb_true_iff in H12 as [H1 H2].
    apply fnfa_state_eqb_sound in H1.
    apply fnfa_state_eqb_sound in H2.
    apply fnfa_state_eqb_sound in Hthird.
    unfold triple_first, triple_second, triple_third in *.
    simpl in H1, H2, Hthird.
    subst. reflexivity.
  Qed.

  Lemma g3_edgeb_sound :
    forall (m : @finite_nfa A) x y,
      g3_edgeb m x y = true ->
      exists a,
        In a (fnfa_alphabet m) /\
        In (triple_first m y)
          (nfa_step (fnfa_base m) (triple_first m x) a) /\
        In (triple_second m y)
          (nfa_step (fnfa_base m) (triple_second m x) a) /\
        In (triple_third m y)
          (nfa_step (fnfa_base m) (triple_third m x) a).
  Proof.
    intros m x y H.
    unfold g3_edgeb in H.
    apply existsb_exists in H as [a [Ha Hsteps]].
    apply andb_true_iff in Hsteps as [H12 H3].
    apply andb_true_iff in H12 as [H1 H2].
    exists a. repeat split; auto;
      now apply step_to_stateb_sound.
  Qed.

  Lemma g3_walk_paths :
    forall (m : @finite_nfa A) x y,
      walk (g3_edgeb m) x y ->
      exists w,
        finite_delta_star m (triple_first m x) w (triple_first m y) /\
        finite_delta_star m (triple_second m x) w (triple_second m y) /\
        finite_delta_star m (triple_third m x) w (triple_third m y).
  Proof.
    intros m x y Hwalk.
    induction Hwalk as [x| x y z Hedge _ [w [H1 [H2 H3]]]].
    - exists []. repeat split; constructor.
    - destruct x as [[x1 x2] x3].
      destruct y as [[y1 y2] y3].
      destruct z as [[z1 z2] z3].
      simpl in *.
      destruct (g3_edgeb_sound m ((x1, x2), x3) ((y1, y2), y3) Hedge)
        as [a [_ [Hstep1 [Hstep2 Hstep3]]]].
      exists (a :: w).
      repeat split; eapply Path_cons; eauto.
  Qed.

  Theorem idab_graph_sound :
    forall (m : @finite_nfa A),
      idab_graph m = true -> IDA m.
  Proof.
    intros m H.
    unfold idab_graph in H.
    apply existsb_exists in H as [p [_ Hp]].
    apply existsb_exists in Hp as [q [_ Hq]].
    apply andb_true_iff in Hq as [Hleft Hreach].
    apply andb_true_iff in Hleft as [Hleft Huseful_q].
    apply andb_true_iff in Hleft as [Hneq Huseful_p].
    apply negb_true_iff in Hneq.
    assert (Hdiff : p <> q).
    {
      intros Heq.
      subst q.
      simpl in Hneq.
      rewrite (fnfa_state_eqb_complete m p p eq_refl) in Hneq.
      discriminate.
    }
    apply usefulb_graph_sound in Huseful_p.
    apply usefulb_graph_sound in Huseful_q.
    pose proof
      (@reachb_sound
         (state_triple m)
         (state_triple_eqb m)
         (state_triple_eqb_sound m)
         (state_triple_vertices m)
         (g3_edgeb m)
         (length (state_triple_vertices m))
         ((p, p), q) ((p, q), q) Hreach) as Hwalk.
    destruct (g3_walk_paths m ((p, p), q) ((p, q), q) Hwalk)
      as [v [Hpp [Hpq Hqq]]].
    exists p, q, v.
    repeat split; assumption.
  Qed.

  Theorem degree_growthb_exponential_sound :
    forall (m : @finite_nfa A),
      degree_growthb m = ExponentialAmbiguity -> EDA m.
  Proof.
    intros m H.
    unfold degree_growthb in H.
    destruct (edab_graph m) eqn:Heda.
    - now apply edab_graph_sound.
    - destruct (ida_degree_lower_boundb m); discriminate.
  Qed.

  Lemma lists_of_length_length :
    forall {B : Type} (xs : list B) n ys,
      In ys (lists_of_length xs n) ->
      length ys = n.
  Proof.
    intros B xs n.
    induction n as [| n IH]; intros ys Hin; simpl in Hin.
    - destruct Hin as [Heq | []]. subst. reflexivity.
    - apply in_concat in Hin as [yss [Hyss Hys]].
      apply in_map_iff in Hyss as [x [Hx _]].
      subst yss.
      apply in_map_iff in Hys as [ys' [Hys Hys']].
      subst ys.
      simpl. now rewrite (IH ys' Hys').
  Qed.

  Lemma ida_layerb_sound :
    forall fuel (m : @finite_nfa A) l,
      ida_layerb fuel m l = true ->
      IDA_layer m l.
  Proof.
    intros fuel m l H.
    unfold ida_layerb in H.
    set (r := layer_left m l) in *.
    set (s := layer_right m l) in *.
    set (v := layer_word m l) in *.
    apply andb_true_iff in H as [Hneq H].
    apply andb_true_iff in H as [Hur H].
    apply andb_true_iff in H as [Hus H].
    apply andb_true_iff in H as [Hrr H].
    apply andb_true_iff in H as [Hrs Hss].
    change
      (r <> s /\
       finite_useful m r /\
       finite_useful m s /\
       finite_delta_star m r v r /\
       finite_delta_star m r v s /\
       finite_delta_star m s v s).
    repeat split.
    - intros Heq.
      apply negb_true_iff in Hneq.
      rewrite (fnfa_state_eqb_complete m r s Heq) in Hneq.
      discriminate.
    - now apply usefulb_with_fuel_sound with (fuel := fuel).
    - now apply usefulb_with_fuel_sound with (fuel := fuel).
    - now apply pathb_sound.
    - now apply pathb_sound.
    - now apply pathb_sound.
  Qed.

  Lemma ida_layersb_sound :
    forall fuel (m : @finite_nfa A) layers,
      ida_layersb fuel m layers = true ->
      Forall (IDA_layer m) layers.
  Proof.
    intros fuel m layers.
    induction layers as [| l layers IH]; simpl; intros H.
    - constructor.
    - apply andb_true_iff in H as [Hl Hlayers].
      constructor.
      + now apply ida_layerb_sound with (fuel := fuel).
      + now apply IH.
  Qed.

  Lemma ida_connectorsb_sound :
    forall (m : @finite_nfa A) layers connectors,
      ida_connectorsb m layers connectors = true ->
      IDA_layer_connectors m layers connectors.
  Proof.
    intros m layers.
    induction layers as [| l1 layers IH]; intros connectors H; simpl in *.
    - destruct connectors; simpl in H; try discriminate; exact I.
    - destruct layers as [| l2 rest].
      + destruct connectors; simpl in H; try discriminate; exact I.
      + destruct connectors as [| u us]; simpl in H; try discriminate.
        apply andb_true_iff in H as [Hu Hus].
        split.
        * now apply pathb_sound.
        * now apply IH.
  Qed.

  Theorem idadb_with_fuel_sound :
    forall fuel d (m : @finite_nfa A),
      idadb_with_fuel fuel d m = true ->
      IDA_d m d.
  Proof.
    intros fuel d m H.
    unfold idadb_with_fuel in H.
    apply existsb_exists in H as [layers [Hlayers Hlayers_ok]].
    apply existsb_exists in Hlayers_ok as [connectors [Hconnectors Hok]].
    apply andb_true_iff in Hok as [Hls Hus].
    exists layers, connectors.
    repeat split.
    - eapply lists_of_length_length; eauto.
    - eapply lists_of_length_length; eauto.
    - now apply ida_layersb_sound with (fuel := fuel).
    - now apply ida_connectorsb_sound.
  Qed.

  Lemma IDA_d_one_of_IDA :
    forall (m : @finite_nfa A),
      IDA m ->
      IDA_d m 1.
  Proof.
    intros m H.
    destruct H as [p [q [v [Hneq [Hup [Huq [Hpp [Hpq Hqq]]]]]]]].
    exists [((p, q), v)], [].
    simpl.
    repeat split; auto.
    constructor.
    - simpl; repeat split; assumption.
    - constructor.
  Qed.

  Theorem ida_db_graph_one_sound :
    forall (m : @finite_nfa A),
      idab_graph m = true -> IDA_d m 1.
  Proof.
    intros m H.
    apply IDA_d_one_of_IDA.
    now apply idab_graph_sound.
  Qed.

  Lemma IDA_accepting_runs_from_lower :
    forall (m : @finite_nfa A) p q v suffix n,
      p <> q ->
      0 < da_from_to m p v p ->
      0 < da_from_to m p v q ->
      0 < da_from_to m q v q ->
      0 < accepting_runs_from (fnfa_base m) q suffix ->
      S n <=
      accepting_runs_from
        (fnfa_base m) p (word_power v (S n) ++ suffix).
  Proof.
    intros m p q v suffix n Hneq Hpp Hpq Hqq Hsuffix.
    induction n as [| n IH].
    - simpl.
      rewrite app_nil_r.
      pose proof (accepting_runs_from_app_lower m p v q suffix) as Hlower.
      assert (Hprod :
        1 <= da_from_to m p v q *
             accepting_runs_from (fnfa_base m) q suffix).
      { apply Nat.mul_pos_pos; assumption. }
      unfold da_from_to in *.
      lia.
    - simpl.
      rewrite <- app_assoc.
      pose proof
        (accepting_runs_from_app_lower_two
           m p q p v (word_power v (S n) ++ suffix) Hneq)
        as Htwo.
      pose proof
        (accepting_runs_from_word_power_lower
           m q v (S n) suffix 1) as Hq_lower.
      assert (Hq_count : 1 <= da_from_to m q v q) by lia.
      specialize (Hq_lower Hq_count).
      assert (Hpow1 : Nat.pow 1 (S n) = 1).
      {
        assert (Hpow1_all : forall k, Nat.pow 1 k = 1).
        {
          induction k as [| k IHk]; simpl; auto.
          now rewrite IHk.
        }
        apply Hpow1_all.
      }
      rewrite Hpow1 in Hq_lower. simpl in Hq_lower.
      replace (accepting_runs_from (fnfa_base m) q suffix + 0)
        with (accepting_runs_from (fnfa_base m) q suffix)
        in Hq_lower by lia.
      change
        (accepting_runs_from
           (fnfa_base m) q ((v ++ word_power v n) ++ suffix))
        with
        (accepting_runs_from
           (fnfa_base m) q (word_power v (S n) ++ suffix))
        in Hq_lower.
      assert (Hq_suffix :
        1 <= accepting_runs_from
               (fnfa_base m) q (word_power v (S n) ++ suffix)).
      {
        eapply Nat.le_trans.
        - exact Hsuffix.
        - exact Hq_lower.
      }
      assert (Hp_part :
        S n <= da_from_to m p v p *
               accepting_runs_from
                 (fnfa_base m) p (word_power v (S n) ++ suffix)).
      {
        pose proof
          (Nat.mul_le_mono
             1
             (da_from_to m p v p)
             (S n)
             (accepting_runs_from
                (fnfa_base m) p (word_power v (S n) ++ suffix)))
          as Hmul.
        specialize (Hmul ltac:(lia) IH).
        simpl in Hmul.
        replace (S (n + 0)) with (S n) in Hmul by lia.
        change
          (accepting_runs_from
             (fnfa_base m) p ((v ++ word_power v n) ++ suffix))
          with
          (accepting_runs_from
             (fnfa_base m) p (word_power v (S n) ++ suffix))
          in Hmul.
        exact Hmul.
      }
      assert (Hq_part :
        1 <= da_from_to m p v q *
             accepting_runs_from
               (fnfa_base m) q (word_power v (S n) ++ suffix)).
      { apply Nat.mul_pos_pos; lia. }
      unfold da_from_to in *.
      assert (Hsum :
        S (S n) <=
        runs_between m p v p *
        accepting_runs_from
          (fnfa_base m) p (word_power v (S n) ++ suffix) +
        runs_between m p v q *
        accepting_runs_from
          (fnfa_base m) q (word_power v (S n) ++ suffix)).
      { lia. }
      eapply Nat.le_trans; eauto.
  Qed.

  Theorem IDA_infinitely_ambiguous :
    forall (m : @finite_nfa A),
      IDA m ->
      infinitely_ambiguous (fnfa_base m).
  Proof.
    intros m Hida k.
    destruct Hida as [p [q [v [Hneq [Hup [Huq [Hpp [Hpq Hqq]]]]]]]].
    destruct (useful_state_positive_tests m p Hup)
      as [prefix [_ [Hprefix _]]].
    destruct (useful_state_positive_tests m q Huq)
      as [_ [suffix [_ Hsuffix]]].
    exists (prefix ++ word_power v (S k) ++ suffix).
    pose proof (path_runs_between_positive m p v p Hpp) as Hpp_count.
    pose proof (path_runs_between_positive m p v q Hpq) as Hpq_count.
    pose proof (path_runs_between_positive m q v q Hqq) as Hqq_count.
    pose proof
      (IDA_accepting_runs_from_lower
         m p q v suffix k Hneq Hpp_count Hpq_count Hqq_count Hsuffix)
      as Hpump.
    pose proof
      (ambiguity_of_word_app_lower
         m prefix p (word_power v (S k) ++ suffix))
      as Hamb.
    assert (Hleft :
      k <= start_runs_to m prefix p *
           accepting_runs_from
             (fnfa_base m) p (word_power v (S k) ++ suffix)).
    {
      assert (Hsk :
        S k <= start_runs_to m prefix p *
               accepting_runs_from
                 (fnfa_base m) p (word_power v (S k) ++ suffix)).
      {
        pose proof
          (Nat.mul_le_mono
             1
             (start_runs_to m prefix p)
             (S k)
             (accepting_runs_from
                (fnfa_base m) p (word_power v (S k) ++ suffix)))
          as Hmul.
        specialize (Hmul ltac:(lia) Hpump).
        replace (1 * S k) with (S k) in Hmul by lia.
        exact Hmul.
      }
      lia.
    }
    lia.
  Qed.

  Theorem EDA_exponential_ambiguity_lower_bound :
    forall (m : @finite_nfa A),
      EDA m ->
      exponential_ambiguity_lower_bound (fnfa_base m).
  Proof.
    intros m Heda.
    destruct Heda as [q [v [Huseful [_ Hcount]]]].
    destruct (useful_state_positive_tests m q Huseful)
      as [prefix [suffix [Hprefix Hsuffix]]].
    exists prefix, v, suffix.
    intros n.
    pose proof
      (ambiguity_of_word_word_power_lower
         m prefix q v n suffix 2 Hcount) as Hlower.
    eapply Nat.le_trans.
    - apply nat_le_mul_with_positive.
      + exact Hprefix.
      + exact Hsuffix.
    - exact Hlower.
  Qed.

  Corollary edab_with_fuel_exponential_ambiguity_lower_bound :
    forall fuel (m : @finite_nfa A),
      edab_with_fuel fuel m = true ->
      exponential_ambiguity_lower_bound (fnfa_base m).
  Proof.
    intros fuel m H.
    apply EDA_exponential_ambiguity_lower_bound.
    now apply edab_with_fuel_sound with (fuel := fuel).
  Qed.
End InfiniteAmbiguity.
