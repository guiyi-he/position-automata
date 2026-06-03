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

  Definition state_reach_relation
      (m : @finite_nfa A) : list (finite_state m * finite_state m) :=
    reachability_relation
      (fnfa_state_eqb m)
      (fnfa_states m)
      (transitionb m)
      (length (fnfa_states m)).

  Definition state_reachb_in
      (m : @finite_nfa A)
      (rel : list (finite_state m * finite_state m))
      (p q : finite_state m) : bool :=
    pair_inb (fnfa_state_eqb m) p q rel.

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

  Definition g3_reach_relation
      (m : @finite_nfa A) : list (state_triple m * state_triple m) :=
    reachability_relation
      (state_triple_eqb m)
      (state_triple_vertices m)
      (g3_edgeb m)
      (length (state_triple_vertices m)).

  Definition g3_reachb_in
      (m : @finite_nfa A)
      (rel : list (state_triple m * state_triple m))
      (x y : state_triple m) : bool :=
    pair_inb (state_triple_eqb m) x y rel.

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
    g5_redgeb m ci cj
    || (negb (state_connectedb m ci cj) && state_reachb m ci cj).

  Definition same_sccb
      (m : @finite_nfa A)
      (p q : finite_state m) : bool :=
    state_connectedb m p q.

  Definition add_scc_rep
      (m : @finite_nfa A)
      (q : finite_state m)
      (reps : list (finite_state m)) : list (finite_state m) :=
    if existsb (same_sccb m q) reps then reps else q :: reps.

  Definition scc_representatives (m : @finite_nfa A)
      : list (finite_state m) :=
    fold_right (add_scc_rep m) [] (fnfa_states m).

  Definition g5_vertices (m : @finite_nfa A)
      : list (finite_state m) :=
    scc_representatives m.

  Definition g5_degree_lower_boundb (m : @finite_nfa A) : nat :=
    let vertices := g5_vertices m in
    let state_rel := state_reach_relation m in
    let g3_rel := g3_reach_relation m in
    let state_reachc := state_reachb_in m state_rel in
    let state_connectedc :=
      fun p q => state_reachc p q && state_reachc q p in
    let usefulc :=
      fun q =>
        existsb
          (fun q0 => state_reachc q0 q)
          (nfa_start (fnfa_base m))
        &&
        existsb
          (fun qf => nfa_final (fnfa_base m) qf && state_reachc q qf)
          (fnfa_states m) in
    let redge :=
      fun ci cj =>
        existsb
          (fun p =>
             state_connectedc ci p
             &&
             usefulc p
             &&
             existsb
               (fun q =>
                  state_connectedc cj q
                  &&
                  usefulc q
                  &&
                  negb (fnfa_state_eqb m p q)
                  &&
                  g3_reachb_in m g3_rel ((p, p), q) ((p, q), q))
               (fnfa_states m))
          (fnfa_states m) in
    let edge :=
      fun ci cj =>
        redge ci cj
        || (negb (state_connectedc ci cj) && state_reachc ci cj) in
    max_special_edges
      vertices
      edge
      redge
      (length vertices).

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

  Lemma state_inb_complete :
    forall (m : @finite_nfa A) q,
      In q (fnfa_states m) ->
      state_inb m q = true.
  Proof.
    intros m q Hin.
    unfold state_inb.
    apply existsb_exists.
    exists q. split; auto.
    apply fnfa_state_eqb_complete. reflexivity.
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

  Lemma step_to_stateb_complete :
    forall (m : @finite_nfa A) q a q',
      In q' (nfa_step (fnfa_base m) q a) ->
      step_to_stateb m q a q' = true.
  Proof.
    intros m q a q' Hin.
    unfold step_to_stateb.
    apply existsb_exists.
    exists q'. split; auto.
    apply fnfa_state_eqb_complete. reflexivity.
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

  Lemma transitionb_complete :
    forall (m : @finite_nfa A) q a q',
      finite_nfa_wf m ->
      In q (fnfa_states m) ->
      In q' (nfa_step (fnfa_base m) q a) ->
      transitionb m q q' = true.
  Proof.
    intros m q a q' Hwf Hq Hstep.
    unfold transitionb.
    apply existsb_exists.
    exists a. split.
    - eapply finite_nfa_wf_step_in_alphabet; eauto.
    - now apply step_to_stateb_complete.
  Qed.

  Lemma transitionb_closed :
    forall (m : @finite_nfa A) q q',
      finite_nfa_wf m ->
      In q (fnfa_states m) ->
      transitionb m q q' = true ->
      In q' (fnfa_states m).
  Proof.
    intros m q q' Hwf Hq Htrans.
    destruct (transitionb_sound m q q' Htrans) as [a [_ Hstep]].
    eapply finite_nfa_wf_step_in_states; eauto.
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

  Lemma path_transition_walk :
    forall (m : @finite_nfa A) p w q,
      finite_nfa_wf m ->
      In p (fnfa_states m) ->
      finite_delta_star m p w q ->
      walk (transitionb m) p q.
  Proof.
    intros m p w q Hwf Hpin Hpath.
    induction Hpath as [q| q a q' w q'' Hstep _ IH].
    - constructor.
    - eapply Walk_step.
      + eapply transitionb_complete; eauto.
      + apply IH.
        eapply finite_nfa_wf_step_in_states; eauto.
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

  Lemma state_reachb_complete_path :
    forall (m : @finite_nfa A) p w q,
      finite_nfa_wf m ->
      In p (fnfa_states m) ->
      finite_delta_star m p w q ->
      state_reachb m p q = true.
  Proof.
    intros m p w q Hwf Hpin Hpath.
    unfold state_reachb.
    eapply (@reachb_complete
      (finite_state m)
      (fnfa_state_eqb m)
      (fun x y Heq => fnfa_state_eqb_complete m x y Heq)
      (fnfa_states m)
      (transitionb m)
      (length (fnfa_states m))
      p q).
    - apply le_n.
    - exact Hpin.
    - intros x y Hx Hedge.
      eapply transitionb_closed; eauto.
    - eapply path_transition_walk; eauto.
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

  Lemma usefulb_graph_complete :
    forall (m : @finite_nfa A) q,
      finite_nfa_wf m ->
      finite_useful m q ->
      usefulb_graph m q = true.
  Proof.
    intros m q Hwf Huseful.
    destruct Huseful as [q0 [qf [w_in [w_out
      [Hstart [Hpath_in [Hpath_out Hfinal]]]]]]].
    assert (Hq0 : In q0 (fnfa_states m)).
    { eapply finite_nfa_wf_start_in_states; eauto. }
    assert (Hq : In q (fnfa_states m)).
    { eapply finite_nfa_wf_path_end_in_states; eauto. }
    assert (Hqf : In qf (fnfa_states m)).
    { eapply finite_nfa_wf_path_end_in_states; eauto. }
    unfold usefulb_graph.
    apply andb_true_iff. split.
    - apply existsb_exists.
      exists q0. split; auto.
      eapply state_reachb_complete_path; eauto.
    - apply existsb_exists.
      exists qf. split; auto.
      apply andb_true_iff. split; auto.
      eapply state_reachb_complete_path; eauto.
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

  Lemma state_pair_eqb_complete :
    forall (m : @finite_nfa A) (x y : state_pair m),
      x = y -> state_pair_eqb m x y = true.
  Proof.
    intros m [x1 x2] [y1 y2] H. inversion H; subst.
    unfold state_pair_eqb. simpl.
    rewrite (fnfa_state_eqb_complete m y1 y1 eq_refl).
    rewrite (fnfa_state_eqb_complete m y2 y2 eq_refl).
    reflexivity.
  Qed.

  Lemma state_pair_vertices_complete :
    forall (m : @finite_nfa A) p q,
      In p (fnfa_states m) ->
      In q (fnfa_states m) ->
      In (p, q) (state_pair_vertices m).
  Proof.
    intros m p q Hp Hq.
    unfold state_pair_vertices.
    now apply in_prod.
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

  Lemma g2_edgeb_complete :
    forall (m : @finite_nfa A) x y a,
      In a (fnfa_alphabet m) ->
      In (fst y) (nfa_step (fnfa_base m) (fst x) a) ->
      In (snd y) (nfa_step (fnfa_base m) (snd x) a) ->
      g2_edgeb m x y = true.
  Proof.
    intros m x y a Ha H1 H2.
    unfold g2_edgeb.
    apply existsb_exists.
    exists a. split; auto.
    apply andb_true_iff. split;
      now apply step_to_stateb_complete.
  Qed.

  Lemma g2_edgeb_closed :
    forall (m : @finite_nfa A) x y,
      finite_nfa_wf m ->
      In x (state_pair_vertices m) ->
      g2_edgeb m x y = true ->
      In y (state_pair_vertices m).
  Proof.
    intros m [x1 x2] [y1 y2] Hwf Hx Hedge.
    unfold state_pair_vertices in Hx.
    apply in_prod_iff in Hx as [Hx1 Hx2].
    destruct (g2_edgeb_sound m (x1, x2) (y1, y2) Hedge)
      as [a [_ [Hstep1 Hstep2]]].
    apply state_pair_vertices_complete.
    - eapply finite_nfa_wf_step_in_states with (q := x1) (a := a); eauto.
    - eapply finite_nfa_wf_step_in_states with (q := x2) (a := a); eauto.
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

  Lemma g2_paths_walk :
    forall (m : @finite_nfa A) p1 p2 w q1 q2,
      finite_nfa_wf m ->
      In p1 (fnfa_states m) ->
      In p2 (fnfa_states m) ->
      finite_delta_star m p1 w q1 ->
      finite_delta_star m p2 w q2 ->
      walk (g2_edgeb m) (p1, p2) (q1, q2).
  Proof.
    intros m p1 p2 w q1 q2 Hwf Hp1 Hp2 Hpath1.
    revert p2 q2 Hp2.
    induction Hpath1 as [q1| p1 a p1' w q1 Hstep1 _ IH];
      intros p2 q2 Hp2 Hpath2.
    - inversion Hpath2; subst. constructor.
    - inversion Hpath2 as [| p2' a' q2' w' q2'' Hstep2 Htail2]; subst.
      eapply Walk_step with (y := (p1', q2')).
      + eapply g2_edgeb_complete.
        * eapply finite_nfa_wf_step_in_alphabet; eauto.
        * exact Hstep1.
        * exact Hstep2.
      + apply IH.
        * eapply finite_nfa_wf_step_in_states with (q := p1) (a := a); eauto.
        * eapply finite_nfa_wf_step_in_states with (q := p2) (a := a); eauto.
        * exact Htail2.
  Qed.

  Lemma g2_reachb_complete_paths :
    forall (m : @finite_nfa A) x y w,
      finite_nfa_wf m ->
      In (fst x) (fnfa_states m) ->
      In (snd x) (fnfa_states m) ->
      finite_delta_star m (fst x) w (fst y) ->
      finite_delta_star m (snd x) w (snd y) ->
      g2_reachb m x y = true.
  Proof.
    intros m [x1 x2] [y1 y2] w Hwf Hx1 Hx2 Hpath1 Hpath2.
    unfold g2_reachb.
    eapply (@reachb_complete
      (state_pair m)
      (state_pair_eqb m)
      (fun a b Hab => state_pair_eqb_complete m a b Hab)
      (state_pair_vertices m)
      (g2_edgeb m)
      (length (state_pair_vertices m))
      (x1, x2) (y1, y2)).
    - apply le_n.
    - apply state_pair_vertices_complete; assumption.
    - intros a b Ha Hedge.
      eapply g2_edgeb_closed; eauto.
    - eapply g2_paths_walk; eauto.
  Qed.

  Lemma g2_connectedb_complete_paths :
    forall (m : @finite_nfa A) x y u v,
      finite_nfa_wf m ->
      In (fst x) (fnfa_states m) ->
      In (snd x) (fnfa_states m) ->
      In (fst y) (fnfa_states m) ->
      In (snd y) (fnfa_states m) ->
      finite_delta_star m (fst x) u (fst y) ->
      finite_delta_star m (snd x) u (snd y) ->
      finite_delta_star m (fst y) v (fst x) ->
      finite_delta_star m (snd y) v (snd x) ->
      g2_connectedb m x y = true.
  Proof.
    intros m [x1 x2] [y1 y2] u v Hwf Hx1 Hx2 Hy1 Hy2 Hxy1 Hxy2 Hyx1 Hyx2.
    unfold g2_connectedb.
    eapply (@connectedb_complete
      (state_pair m)
      (state_pair_eqb m)
      (fun a b Hab => state_pair_eqb_complete m a b Hab)
      (state_pair_vertices m)
      (g2_edgeb m)
      (length (state_pair_vertices m))
      (x1, x2) (y1, y2)).
    - apply le_n.
    - apply state_pair_vertices_complete; assumption.
    - apply state_pair_vertices_complete; assumption.
    - intros a b Ha Hedge.
      eapply g2_edgeb_closed; eauto.
    - eapply g2_paths_walk; eauto.
    - eapply g2_paths_walk; eauto.
  Qed.

  Lemma runs_between_two_sync_paths :
    forall (m : @finite_nfa A) q w r,
      finite_nfa_wf m ->
      In q (fnfa_states m) ->
      2 <= runs_between m q w r ->
      exists p s u v,
        p <> s /\
        finite_delta_star m q u p /\
        finite_delta_star m q u s /\
        finite_delta_star m p v r /\
        finite_delta_star m s v r.
  Proof.
    intros m q w.
    revert q.
    induction w as [| a w IH]; intros q r Hwf Hq Htwo; simpl in Htwo.
    - destruct (fnfa_state_eqb m q r); lia.
    - pose proof
        (finite_nfa_wf_step_targets_NoDup m q a Hwf Hq)
        as Hnodup.
      destruct
        (sum_map_ge_two_cases
           (fun s => runs_between m s w r)
           (nfa_step (fnfa_base m) q a)
           Hnodup
           Htwo)
        as [[mid [Hmid Hmid_two]] |
            [p [s [Hp [Hs [Hneq [Hp_pos Hs_pos]]]]]]].
      + assert (Hmid_state : In mid (fnfa_states m)).
        { eapply finite_nfa_wf_step_in_states; eauto. }
        destruct (IH mid r Hwf Hmid_state Hmid_two)
          as [p [s [u [v [Hneq [Hup [Hus [Hpv Hsv]]]]]]]].
        exists p, s, (a :: u), v.
        split; [exact Hneq |].
        split.
        * eapply Path_cons with (q' := mid); eauto.
        * split.
          -- eapply Path_cons with (q' := mid); eauto.
          -- repeat split; assumption.
      + exists p, s, [a], w.
        split; [exact Hneq |].
        split.
        * eapply Path_cons with (q' := p); eauto. constructor.
        * split.
          -- eapply Path_cons with (q' := s); eauto. constructor.
          -- split.
             ++ apply runs_between_positive_path. exact Hp_pos.
             ++ apply runs_between_positive_path. exact Hs_pos.
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

  Theorem edab_graph_complete :
    forall (m : @finite_nfa A),
      finite_nfa_wf m ->
      EDA m ->
      edab_graph m = true.
  Proof.
    intros m Hwf Heda.
    destruct Heda as [q [v [Huseful [_ Hcount]]]].
    assert (Hq : In q (fnfa_states m)).
    { eapply finite_nfa_wf_useful_in_states; eauto. }
    destruct (runs_between_two_sync_paths m q v q Hwf Hq Hcount)
      as [p [r [u [w [Hdiff [Hqp [Hqr [Hpq Hrq]]]]]]]].
    assert (Hp : In p (fnfa_states m)).
    { eapply finite_nfa_wf_path_end_in_states with (p := q) (w := u); eauto. }
    assert (Hr : In r (fnfa_states m)).
    { eapply finite_nfa_wf_path_end_in_states with (p := q) (w := u); eauto. }
    unfold edab_graph.
    apply existsb_exists.
    exists q. split; auto.
    apply andb_true_iff. split.
    - eapply usefulb_graph_complete; eauto.
    - apply existsb_exists.
      exists (p, r). split.
      + apply state_pair_vertices_complete; assumption.
      + apply andb_true_iff. split.
        * apply negb_true_iff.
          apply fnfa_state_eqb_neq_false. exact Hdiff.
        * eapply g2_connectedb_complete_paths; simpl; eauto.
  Qed.

  Theorem edab_graph_iff :
    forall (m : @finite_nfa A),
      finite_nfa_wf m ->
      edab_graph m = true <-> EDA m.
  Proof.
    intros m Hwf. split.
    - apply edab_graph_sound.
    - now apply edab_graph_complete.
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

  Lemma state_triple_eqb_complete :
    forall (m : @finite_nfa A) (x y : state_triple m),
      x = y -> state_triple_eqb m x y = true.
  Proof.
    intros m [[x1 x2] x3] [[y1 y2] y3] H. inversion H; subst.
    unfold state_triple_eqb, triple_first, triple_second, triple_third.
    simpl.
    rewrite (fnfa_state_eqb_complete m y1 y1 eq_refl).
    rewrite (fnfa_state_eqb_complete m y2 y2 eq_refl).
    rewrite (fnfa_state_eqb_complete m y3 y3 eq_refl).
    reflexivity.
  Qed.

  Lemma state_triple_vertices_complete :
    forall (m : @finite_nfa A) p q r,
      In p (fnfa_states m) ->
      In q (fnfa_states m) ->
      In r (fnfa_states m) ->
      In ((p, q), r) (state_triple_vertices m).
  Proof.
    intros m p q r Hp Hq Hr.
    unfold state_triple_vertices.
    apply in_concat.
    exists (concat
      (map
        (fun q0 => map (fun r0 => ((p, q0), r0)) (fnfa_states m))
        (fnfa_states m))).
    split.
    - apply in_map_iff.
      exists p. split; [reflexivity | exact Hp].
    - apply in_concat.
      exists (map (fun r0 => ((p, q), r0)) (fnfa_states m)).
      split.
      + apply in_map_iff.
        exists q. split; [reflexivity | exact Hq].
      + apply in_map_iff.
        exists r. split; [reflexivity | exact Hr].
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

  Lemma g3_edgeb_complete :
    forall (m : @finite_nfa A) x y a,
      In a (fnfa_alphabet m) ->
      In (triple_first m y)
        (nfa_step (fnfa_base m) (triple_first m x) a) ->
      In (triple_second m y)
        (nfa_step (fnfa_base m) (triple_second m x) a) ->
      In (triple_third m y)
        (nfa_step (fnfa_base m) (triple_third m x) a) ->
      g3_edgeb m x y = true.
  Proof.
    intros m x y a Ha H1 H2 H3.
    unfold g3_edgeb.
    apply existsb_exists.
    exists a. split; auto.
    repeat rewrite andb_true_iff.
    repeat split; now apply step_to_stateb_complete.
  Qed.

  Lemma state_triple_vertices_sound :
    forall (m : @finite_nfa A) x,
      In x (state_triple_vertices m) ->
      In (triple_first m x) (fnfa_states m) /\
      In (triple_second m x) (fnfa_states m) /\
      In (triple_third m x) (fnfa_states m).
  Proof.
    intros m [[p q] r] H.
    unfold state_triple_vertices in H.
    apply in_concat in H as [qs [Hqs Hr]].
    apply in_map_iff in Hqs as [p0 [Hqs Hp]].
    subst qs.
    apply in_concat in Hr as [rs [Hrs Hr]].
    apply in_map_iff in Hrs as [q0 [Hrs Hq]].
    subst rs.
    apply in_map_iff in Hr as [r0 [Hr Hr0]].
    inversion Hr; subst.
    repeat split; assumption.
  Qed.

  Lemma g3_edgeb_closed :
    forall (m : @finite_nfa A) x y,
      finite_nfa_wf m ->
      In x (state_triple_vertices m) ->
      g3_edgeb m x y = true ->
      In y (state_triple_vertices m).
  Proof.
    intros m x y Hwf Hx Hedge.
    destruct (state_triple_vertices_sound m x Hx) as [Hx1 [Hx2 Hx3]].
    destruct (g3_edgeb_sound m x y Hedge)
      as [a [_ [Hstep1 [Hstep2 Hstep3]]]].
    destruct y as [[y1 y2] y3].
    apply state_triple_vertices_complete.
    - eapply finite_nfa_wf_step_in_states
        with (q := triple_first m x) (a := a); eauto.
    - eapply finite_nfa_wf_step_in_states
        with (q := triple_second m x) (a := a); eauto.
    - eapply finite_nfa_wf_step_in_states
        with (q := triple_third m x) (a := a); eauto.
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

  Lemma g3_paths_walk :
    forall (m : @finite_nfa A) p1 p2 p3 w q1 q2 q3,
      finite_nfa_wf m ->
      In p1 (fnfa_states m) ->
      In p2 (fnfa_states m) ->
      In p3 (fnfa_states m) ->
      finite_delta_star m p1 w q1 ->
      finite_delta_star m p2 w q2 ->
      finite_delta_star m p3 w q3 ->
      walk (g3_edgeb m) ((p1, p2), p3) ((q1, q2), q3).
  Proof.
    intros m p1 p2 p3 w q1 q2 q3 Hwf Hp1 Hp2 Hp3 Hpath1.
    revert p2 p3 q2 q3 Hp2 Hp3.
    induction Hpath1 as [q1| p1 a p1' w q1 Hstep1 _ IH];
      intros p2 p3 q2 q3 Hp2 Hp3 Hpath2 Hpath3.
    - inversion Hpath2; subst.
      inversion Hpath3; subst.
      constructor.
    - inversion Hpath2 as [| p2' a2 p2'' w2 q2' Hstep2 Htail2]; subst.
      inversion Hpath3 as [| p3' a3 p3'' w3 q3' Hstep3 Htail3]; subst.
      eapply Walk_step with (y := ((p1', p2''), p3'')).
      + eapply g3_edgeb_complete.
        * eapply finite_nfa_wf_step_in_alphabet; eauto.
        * exact Hstep1.
        * exact Hstep2.
        * exact Hstep3.
      + apply IH.
        * eapply finite_nfa_wf_step_in_states with (q := p1) (a := a); eauto.
        * eapply finite_nfa_wf_step_in_states with (q := p2) (a := a); eauto.
        * eapply finite_nfa_wf_step_in_states with (q := p3) (a := a); eauto.
        * exact Htail2.
        * exact Htail3.
  Qed.

  Lemma g3_reachb_complete_paths :
    forall (m : @finite_nfa A) x y w,
      finite_nfa_wf m ->
      In (triple_first m x) (fnfa_states m) ->
      In (triple_second m x) (fnfa_states m) ->
      In (triple_third m x) (fnfa_states m) ->
      finite_delta_star m (triple_first m x) w (triple_first m y) ->
      finite_delta_star m (triple_second m x) w (triple_second m y) ->
      finite_delta_star m (triple_third m x) w (triple_third m y) ->
      g3_reachb m x y = true.
  Proof.
    intros m [[x1 x2] x3] [[y1 y2] y3] w Hwf Hx1 Hx2 Hx3 Hpath1 Hpath2 Hpath3.
    unfold g3_reachb.
    eapply (@reachb_complete
      (state_triple m)
      (state_triple_eqb m)
      (fun a b Hab => state_triple_eqb_complete m a b Hab)
      (state_triple_vertices m)
      (g3_edgeb m)
      (length (state_triple_vertices m))
      ((x1, x2), x3) ((y1, y2), y3)).
    - apply le_n.
    - apply state_triple_vertices_complete; assumption.
    - intros a b Ha Hedge.
      eapply g3_edgeb_closed; eauto.
    - eapply g3_paths_walk; eauto.
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

  Theorem idab_graph_complete :
    forall (m : @finite_nfa A),
      finite_nfa_wf m ->
      IDA m ->
      idab_graph m = true.
  Proof.
    intros m Hwf Hida.
    destruct Hida as [p [q [v [Hneq [Hup [Huq [Hpp [Hpq Hqq]]]]]]]].
    assert (Hp : In p (fnfa_states m)).
    { eapply finite_nfa_wf_useful_in_states; eauto. }
    assert (Hq : In q (fnfa_states m)).
    { eapply finite_nfa_wf_useful_in_states; eauto. }
    unfold idab_graph.
    apply existsb_exists.
    exists p. split; auto.
    apply existsb_exists.
    exists q. split; auto.
    repeat rewrite andb_true_iff.
    repeat split.
    - apply negb_true_iff.
      apply fnfa_state_eqb_neq_false.
      exact Hneq.
    - eapply usefulb_graph_complete; eauto.
    - eapply usefulb_graph_complete; eauto.
    - eapply g3_reachb_complete_paths; simpl; eauto.
  Qed.

  Theorem idab_graph_iff :
    forall (m : @finite_nfa A),
      finite_nfa_wf m ->
      idab_graph m = true <-> IDA m.
  Proof.
    intros m Hwf. split.
    - apply idab_graph_sound.
    - now apply idab_graph_complete.
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

  Theorem degree_growthb_exponential_complete :
    forall (m : @finite_nfa A),
      finite_nfa_wf m ->
      EDA m ->
      degree_growthb m = ExponentialAmbiguity.
  Proof.
    intros m Hwf Heda.
    unfold degree_growthb.
    rewrite (edab_graph_complete m Hwf Heda).
    reflexivity.
  Qed.

  Theorem degree_growthb_exponential_iff :
    forall (m : @finite_nfa A),
      finite_nfa_wf m ->
      degree_growthb m = ExponentialAmbiguity <-> EDA m.
  Proof.
    intros m Hwf. split.
    - apply degree_growthb_exponential_sound.
    - now apply degree_growthb_exponential_complete.
  Qed.

  Definition degree_growthb_spec
      (m : @finite_nfa A)
      (g : ambiguity_growth) : Prop :=
    match g with
    | ExponentialAmbiguity => EDA m
    | FiniteAmbiguity =>
        ~ EDA m /\ ida_degree_lower_boundb m = 0
    | PolynomialAmbiguity d =>
        ~ EDA m /\ ida_degree_lower_boundb m = d /\ 0 < d
    end.

  Theorem degree_growthb_correct :
    forall (m : @finite_nfa A),
      finite_nfa_wf m ->
      degree_growthb_spec m (degree_growthb m).
  Proof.
    intros m Hwf.
    unfold degree_growthb, degree_growthb_spec.
    destruct (edab_graph m) eqn:Heda.
    - now apply edab_graph_sound.
    - destruct (ida_degree_lower_boundb m) as [| d]; simpl.
      + split; auto.
        intros Hcontra.
        pose proof (edab_graph_complete m Hwf Hcontra) as Heda_true.
        rewrite Heda in Heda_true. discriminate.
      + repeat split; auto; try lia.
        intros Hcontra.
        pose proof (edab_graph_complete m Hwf Hcontra) as Heda_true.
        rewrite Heda in Heda_true. discriminate.
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
