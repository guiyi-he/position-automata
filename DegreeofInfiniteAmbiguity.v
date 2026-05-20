Require Import List Arith Lia.
Import ListNotations.

From PositionAutomata Require Import PositionAutomaton.
From PositionAutomata Require Import DegreeofAmbiguity.

(** The degree of infinite ambiguity of an NFA is the least n such that there
    are infinitely many words with at most n accepting runs.  This file
    contains the definition and basic properties of this notion. *)

Record triple (A : Type) : Type := {
    first : A;
    second : A;
    third : A
}.

Definition State_tuple {A : Type} (m : @automaton A) : Type :=
  triple (state m).


Record intersection_automata {A : Type} (m : @automaton A) : Type := {
  ia_states : list (State_tuple m);
  ia_start : list (State_tuple m);
  ia_final : State_tuple m -> bool;
  ia_step : State_tuple m -> A -> list (State_tuple m)
}.

Fixpoint ComputeAllia_states {A : Type} (m : @automaton A) : list (State_tuple m) :=
  let todo : list (State_tuple m) := [(start m, start m, start m)] in
  let visited := [] in
  match todo with
  | [] => visited
  | s :: todo' =>
  

Fixpoint Intersection_automata (m : @automaton A) : @automaton A :=
  let states := list_prod (list_prod (states m) (states m)) (states m) in
  let start := [(start m, start m, start m)] in
  let final (s : State_tuple) : bool :=
      let '(q1, q2, q3) := s in
      final m q1 && final m q2 && final m q3 in
  let step (s : State_tuple) (a : A) : list State_tuple :=
      let '(q1, q2, q3) := s in
      let next_q1 := step m q1 a in
      let next_q2 := step m q2 a in
      let next_q3 := step m q3 a in
      list_prod (list_prod next_q1 next_q2) next_q3 in
  {| states := states; start := start; final := final; step := step |}.

Fixpoint All_Words_from_P_to_Q 
    (alphabet : list A)
    (P : state)
    (Q : state)
    (m : @automaton A) : list (list A) := 
    match P with
    | [] => []
    | _ => let next_states := map (fun a => step m P a) alphabet in
           let words_from_next := concat (map (fun R => All_Words_from_P_to_Q alphabet R Q m) next_states) in
           let symbols_for_next := concat (map (fun R => map (fun a => [a]) alphabet) next_states) in
           let words_for_next := concat (map (fun R => map (fun a => [a]) alphabet) next_states) in
           if eqbP P Q then [[]] ++ words_from_next ++ words_for_next else words_from_next ++ words_for_next
    end.