Require Import List Arith Lia.
Import ListNotations.

From PositionAutomata Require Import PositionAutomaton.

(** Basic definitions for the degree of ambiguity of finite automata.

    For an NFA, the ambiguity of a word is the number of accepting runs on that
    word.  The degree of ambiguity up to a length bound is the maximum of those
    numbers over all words of that length.  This file keeps the definitions
    intentionally small and executable; later Weber-Seidl style classifications
    can be stated on top of these notions. *)

Fixpoint sum_nats (xs : list nat) : nat :=
  match xs with
  | [] => 0
  | x :: xs' => x + sum_nats xs'
  end.

Fixpoint max_nats (xs : list nat) : nat :=
  match xs with
  | [] => 0
  | x :: xs' => Nat.max x (max_nats xs')
  end.

Lemma sum_nats_singleton :
  forall n, sum_nats [n] = n.
Proof.
  intros n. simpl. lia.
Qed.

Lemma sum_nats_all_le_one :
  forall xs,
    (forall x, In x xs -> x <= 1) ->
    sum_nats xs <= length xs.
Proof.
  intros xs H.
  induction xs as [| x xs IH]; simpl.
  - lia.
  - assert (Hx : x <= 1). 
    {apply H; simpl; auto. }
    assert (Hxs : sum_nats xs <= length xs).
    { apply IH. intros y Hy. apply H. simpl; auto. }
    lia.
Qed.

Section NFA.
  Context {A : Type}.

  Record nfa : Type := {
    nfa_state : Type;
    nfa_start : list nfa_state;
    nfa_final : nfa_state -> bool;
    nfa_step : nfa_state -> A -> list nfa_state
  }.

  Fixpoint accepting_runs_from
      (m : nfa)
      (q : nfa_state m)
      (w : list A) : nat :=
    match w with
    | [] => if nfa_final m q then 1 else 0
    | a :: w' =>
        sum_nats (map (fun q' => accepting_runs_from m q' w') (nfa_step m q a))
    end.

  Definition ambiguity_of_word (m : nfa) (w : list A) : nat :=
    sum_nats (map (fun q => accepting_runs_from m q w) (nfa_start m)).

  Fixpoint words_of_length (alphabet : list A) (n : nat) : list (list A) :=
    match n with
    | O => [[]]
    | S n' =>
        concat
          (map
             (fun a => map (fun w => a :: w) (words_of_length alphabet n'))
             alphabet)
    end.

  Definition ambiguity_on_length
      (alphabet : list A)
      (m : nfa)
      (n : nat) : nat :=
    max_nats (map (ambiguity_of_word m) (words_of_length alphabet n)).

  Definition k_ambiguous (m : nfa) (k : nat) : Prop :=
    forall w, ambiguity_of_word m w <= k.

  Definition unambiguous (m : nfa) : Prop :=
    k_ambiguous m 1.

  Definition finitely_ambiguous (m : nfa) : Prop :=
    exists k, k_ambiguous m k.

  Definition polynomially_ambiguous (m : nfa) : Prop :=
    exists c d,
      forall w, ambiguity_of_word m w <= c * Nat.pow (S (length w)) d.

  Definition exponentially_bounded (m : nfa) : Prop :=
    exists c b,
      2 <= b /\
      forall w, ambiguity_of_word m w <= c * Nat.pow b (length w).

  Definition deterministic_as_nfa (m : @automaton A) : nfa :=
    {|
      nfa_state := state m;
      nfa_start := [start m];
      nfa_final := final m;
      nfa_step := fun q a => [step m q a]
    |}.

  Fixpoint deterministic_run (m : @automaton A) (q : state m) (w : list A)
      : state m :=
    match w with
    | [] => q
    | a :: w' => deterministic_run m (step m q a) w'
    end.

  Lemma accepting_runs_from_deterministic_as_nfa :
    forall (m : @automaton A) q w,
      accepting_runs_from (deterministic_as_nfa m) q w =
        if final m (deterministic_run m q w) then 1 else 0.
  Proof.
    intros m q w.
    revert q.
    induction w as [| a w IH]; intros q; simpl.
    - reflexivity.
    - rewrite IH.
      destruct (final m (deterministic_run m (step m q a) w)); simpl; lia.
  Qed.

  Theorem deterministic_as_nfa_unambiguous :
    forall (m : @automaton A), unambiguous (deterministic_as_nfa m).
  Proof.
    intros m w.
    unfold ambiguity_of_word.
    simpl.
    rewrite accepting_runs_from_deterministic_as_nfa.
    destruct (final m (deterministic_run m (start m) w)); simpl; lia.
  Qed.

  Theorem deterministic_as_nfa_finitely_ambiguous :
    forall (m : @automaton A), finitely_ambiguous (deterministic_as_nfa m).
  Proof.
    intros m. exists 1. apply deterministic_as_nfa_unambiguous.
  Qed.
End NFA.
