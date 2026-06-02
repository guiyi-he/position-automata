From Stdlib Require Import List Bool.
Import ListNotations.

From PositionAutomata Require Import
  Syntax DegreeofAmbiguity DegreeofInfiniteAmbiguity.

(** ReDoS-oriented interface for regular expressions.

    The executable checker is intentionally positive-only: a [true] result
    proves the presence of an EDA witness in the position NFA generated from
    the regex.  A [false] result only means that no witness was found within
    the chosen fuel. *)

Section RegexReDoS.
  Context {A : Type}.

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
