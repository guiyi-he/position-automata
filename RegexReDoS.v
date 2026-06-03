From Stdlib Require Import List Bool Arith Lia.
Import ListNotations.

From PositionAutomata Require Import
  Syntax PositionAutomaton PositionCorrectness
  DegreeofAmbiguity DegreeofInfiniteAmbiguity.

(** ReDoS-oriented interface for regular expressions.

    The executable checker is intentionally positive-only: a [true] result
    proves the presence of an EDA witness in the position NFA generated from
    the regex.  A [false] result only means that no witness was found within
    the chosen fuel. *)

Section RegexReDoS.
  Context {A : Type}.

  Definition position_label_matches_closed
      (alphabet : list A)
      (label_matches : A -> A -> bool)
      (r : positioned_regex A) : Prop :=
    forall p b a,
      In p (positions r) ->
      label_of r p = Some b ->
      label_matches b a = true ->
      In a alphabet.

  Definition label_matches_closed
      (alphabet : list A)
      (label_matches : A -> A -> bool)
      (r : regex A) : Prop :=
    position_label_matches_closed alphabet label_matches (label r).

  Definition position_nfa_steps_nodup
      (label_matches : A -> A -> bool)
      (r : positioned_regex A) : Prop :=
    forall s a, NoDup (position_nfa_step label_matches r s a).

  Definition regex_finite_position_nfa
      (alphabet : list A)
      (label_matches : A -> A -> bool)
      (r : regex A) : finite_nfa :=
    finite_position_nfa alphabet label_matches (label r).

  Definition regex_redos_vulnerable
      (alphabet : list A)
      (label_matches : A -> A -> bool)
      (r : regex A) : Prop :=
    EDA (regex_finite_position_nfa alphabet label_matches r).

  Definition regex_redosb_with_fuel
      (fuel : nat)
      (alphabet : list A)
      (label_matches : A -> A -> bool)
      (r : regex A) : bool :=
    edab_with_fuel
      fuel
      (regex_finite_position_nfa alphabet label_matches r).

  Definition regex_exponential_ambiguity_lower_bound
      (alphabet : list A)
      (label_matches : A -> A -> bool)
      (r : regex A) : Prop :=
    exponential_ambiguity_lower_bound
      (fnfa_base (regex_finite_position_nfa alphabet label_matches r)).

  Definition regex_ambiguity_of_word
      (alphabet : list A)
      (label_matches : A -> A -> bool)
      (r : regex A)
      (w : list A) : nat :=
    ambiguity_of_word
      (fnfa_base (regex_finite_position_nfa alphabet label_matches r))
      w.

  Definition regex_ambiguity_on_length
      (alphabet : list A)
      (label_matches : A -> A -> bool)
      (r : regex A)
      (n : nat) : nat :=
    ambiguity_on_length
      alphabet
      (fnfa_base (regex_finite_position_nfa alphabet label_matches r))
      n.

  Definition regex_redosb_graph
      (alphabet : list A)
      (label_matches : A -> A -> bool)
      (r : regex A) : bool :=
    edab_graph (regex_finite_position_nfa alphabet label_matches r).

  Definition regex_degree_growthb
      (alphabet : list A)
      (label_matches : A -> A -> bool)
      (r : regex A) : ambiguity_growth :=
    degree_growthb (regex_finite_position_nfa alphabet label_matches r).

  Definition regex_redos_classb := regex_degree_growthb.

  Definition regex_exponential_redosb
      (alphabet : list A)
      (label_matches : A -> A -> bool)
      (r : regex A) : bool :=
      match regex_degree_growthb alphabet label_matches r with
    | ExponentialAmbiguity => true
    | _ => false
    end.

  Definition growth_at_leastb
      (threshold actual : ambiguity_growth) : bool :=
    match threshold, actual with
    | FiniteAmbiguity, _ => true
    | PolynomialAmbiguity d, PolynomialAmbiguity e => d <=? e
    | PolynomialAmbiguity _, ExponentialAmbiguity => true
    | ExponentialAmbiguity, ExponentialAmbiguity => true
    | _, _ => false
    end.

  Definition growth_at_least
      (threshold actual : ambiguity_growth) : Prop :=
    match threshold, actual with
    | FiniteAmbiguity, _ => True
    | PolynomialAmbiguity d, PolynomialAmbiguity e => d <= e
    | PolynomialAmbiguity _, ExponentialAmbiguity => True
    | ExponentialAmbiguity, ExponentialAmbiguity => True
    | _, _ => False
    end.

  Definition regex_redosb_at_least
      (threshold : ambiguity_growth)
      (alphabet : list A)
      (label_matches : A -> A -> bool)
      (r : regex A) : bool :=
    growth_at_leastb threshold
      (regex_degree_growthb alphabet label_matches r).

  Lemma matching_positions_in_position_states :
    forall (label_matches : A -> A -> bool) (r : positioned_regex A) ps a s,
      (forall p, In p ps -> In p (positions r)) ->
      In s (matching_positions label_matches (label_of r) ps a) ->
      In s (None :: map Some (positions r)).
  Proof.
    intros label_matches r ps a s Hps Hin.
    destruct (matching_positions_in_state label_matches (label_of r) ps a s Hin)
      as [p [b [Hs [Hmem [_ _]]]]].
    subst s.
    simpl. right.
    apply in_map.
    apply Hps.
    now apply mem_true_In.
  Qed.

  Lemma option_positions_NoDup :
    forall (r : positioned_regex A),
      NoDup (positions r) ->
      NoDup (None :: map Some (positions r)).
  Proof.
    intros r Hnodup.
    constructor.
    - intros Hin.
      apply in_map_iff in Hin as [p [Hp _]].
      discriminate.
    - induction Hnodup as [| p ps Hnotin Hnodup IH]; simpl.
      + constructor.
      + constructor; auto.
        intros Hin.
        apply in_map_iff in Hin as [q [Hq Hqin]].
        inversion Hq; subst.
        contradiction.
  Qed.

  Theorem finite_position_nfa_wf :
    forall alphabet label_matches (r : positioned_regex A),
      NoDup (positions r) ->
      position_label_matches_closed alphabet label_matches r ->
      position_nfa_steps_nodup label_matches r ->
      finite_nfa_wf (finite_position_nfa alphabet label_matches r).
  Proof.
    intros alphabet label_matches r Hnodup Hclosed Hstep_nodup.
    constructor.
    - simpl. now apply option_positions_NoDup.
    - intros q Hq. simpl in Hq. destruct Hq as [Hq | []]. subst.
      simpl. auto.
    - intros q a q' Hq Hstep.
      simpl in Hq, Hstep |- *.
      destruct q as [p|].
      + eapply matching_positions_in_position_states.
        * intros q Hfollow.
          eapply mem_lookup_follow_value_in_positions.
          apply In_mem. exact Hfollow.
        * exact Hstep.
      + eapply matching_positions_in_position_states.
        * intros p Hfirst.
          eapply firstpos_In_positions. exact Hfirst.
        * exact Hstep.
    - intros q a q' Hq Hstep.
      simpl in Hq, Hstep.
      destruct q as [p|].
      + destruct
          (matching_positions_in_state
             label_matches (label_of r) (lookup_follow p (followpos r)) a q'
             Hstep)
          as [p' [b [Hq' [Hmem [Hlbl Hmatch]]]]].
        eapply Hclosed; eauto.
        eapply mem_lookup_follow_value_in_positions; eauto.
      + destruct
          (matching_positions_in_state
             label_matches (label_of r) (firstpos r) a q'
             Hstep)
          as [p' [b [Hq' [Hmem [Hlbl Hmatch]]]]].
        eapply Hclosed; eauto.
        apply firstpos_In_positions.
        now apply mem_true_In.
    - intros q a Hq.
      apply Hstep_nodup.
  Qed.

  Theorem regex_finite_position_nfa_wf :
    forall alphabet label_matches (r : regex A),
      label_matches_closed alphabet label_matches r ->
      position_nfa_steps_nodup label_matches (label r) ->
      finite_nfa_wf (regex_finite_position_nfa alphabet label_matches r).
  Proof.
    intros alphabet label_matches r Hclosed Hnodup_steps.
    unfold regex_finite_position_nfa.
    apply finite_position_nfa_wf; auto.
    apply label_positions_nodup.
  Qed.

  Theorem growth_at_leastb_correct :
    forall threshold actual,
      growth_at_leastb threshold actual = true <->
      growth_at_least threshold actual.
  Proof.
    intros [| d |] [| e |]; simpl.
    - tauto.
    - tauto.
    - tauto.
    - split; intros H; [discriminate | contradiction].
    - apply Nat.leb_le.
    - tauto.
    - split; intros H; [discriminate | contradiction].
    - split; intros H; [discriminate | contradiction].
    - tauto.
  Qed.

  Theorem regex_redosb_at_least_correct :
    forall threshold alphabet label_matches (r : regex A),
      regex_redosb_at_least threshold alphabet label_matches r = true <->
      growth_at_least
        threshold
        (regex_degree_growthb alphabet label_matches r).
  Proof.
    intros threshold alphabet label_matches r.
    unfold regex_redosb_at_least.
    apply growth_at_leastb_correct.
  Qed.

  Theorem regex_redosb_with_fuel_sound :
    forall fuel alphabet label_matches (r : regex A),
      regex_redosb_with_fuel fuel alphabet label_matches r = true ->
      regex_redos_vulnerable alphabet label_matches r.
  Proof.
    intros fuel alphabet label_matches r H.
    unfold regex_redosb_with_fuel, regex_redos_vulnerable in *.
    now apply edab_with_fuel_sound with (fuel := fuel).
  Qed.

  Theorem regex_redosb_graph_sound :
    forall alphabet label_matches (r : regex A),
      regex_redosb_graph alphabet label_matches r = true ->
      regex_redos_vulnerable alphabet label_matches r.
  Proof.
    intros alphabet label_matches r H.
    unfold regex_redosb_graph, regex_redos_vulnerable in *.
    now apply edab_graph_sound.
  Qed.

  Theorem regex_exponential_redosb_sound :
    forall alphabet label_matches (r : regex A),
      regex_exponential_redosb alphabet label_matches r = true ->
      regex_redos_vulnerable alphabet label_matches r.
  Proof.
    intros alphabet label_matches r H.
    unfold regex_exponential_redosb, regex_degree_growthb in H.
    destruct (degree_growthb (regex_finite_position_nfa alphabet label_matches r))
      eqn:Hgrowth; try discriminate.
    unfold regex_redos_vulnerable.
    now apply degree_growthb_exponential_sound.
  Qed.

  Theorem regex_exponential_redosb_complete :
    forall alphabet label_matches (r : regex A),
      finite_nfa_wf (regex_finite_position_nfa alphabet label_matches r) ->
      regex_redos_vulnerable alphabet label_matches r ->
      regex_exponential_redosb alphabet label_matches r = true.
  Proof.
    intros alphabet label_matches r Hwf Hredos.
    unfold regex_exponential_redosb, regex_degree_growthb.
    rewrite (degree_growthb_exponential_complete
      (regex_finite_position_nfa alphabet label_matches r)
      Hwf
      Hredos).
    reflexivity.
  Qed.

  Theorem regex_exponential_redosb_iff :
    forall alphabet label_matches (r : regex A),
      finite_nfa_wf (regex_finite_position_nfa alphabet label_matches r) ->
      regex_exponential_redosb alphabet label_matches r = true <->
      regex_redos_vulnerable alphabet label_matches r.
  Proof.
    intros alphabet label_matches r Hwf. split.
    - apply regex_exponential_redosb_sound.
    - now apply regex_exponential_redosb_complete.
  Qed.

  Theorem regex_redos_vulnerable_exponential_lower :
    forall alphabet label_matches (r : regex A),
      regex_redos_vulnerable alphabet label_matches r ->
      regex_exponential_ambiguity_lower_bound alphabet label_matches r.
  Proof.
    intros alphabet label_matches r H.
    unfold
      regex_redos_vulnerable,
      regex_exponential_ambiguity_lower_bound in *.
    now apply EDA_exponential_ambiguity_lower_bound.
  Qed.

  Corollary regex_redosb_with_fuel_exponential_lower :
    forall fuel alphabet label_matches (r : regex A),
      regex_redosb_with_fuel fuel alphabet label_matches r = true ->
      regex_exponential_ambiguity_lower_bound alphabet label_matches r.
  Proof.
    intros fuel alphabet label_matches r H.
    apply regex_redos_vulnerable_exponential_lower.
    now apply regex_redosb_with_fuel_sound with (fuel := fuel).
  Qed.
End RegexReDoS.
