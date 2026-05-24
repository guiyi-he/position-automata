From Stdlib Require Import List Bool Arith.
Import ListNotations.

From PositionAutomata Require Import
  Syntax PositionAutomaton Equivalence KleeneSemantics
  DegreeofAmbiguity DegreeofInfiniteAmbiguity.

Definition a_then_b : regex bool :=
  Cat (Atom true) (Atom false).

Example label_a_then_b :
  label a_then_b = PCat (PAtom 0 true) (PAtom 1 false).
Proof. reflexivity. Qed.

Definition positioned_a_then_b : positioned_regex bool :=
  label a_then_b.

Example nullable_a_then_b :
  nullable positioned_a_then_b = false.
Proof. reflexivity. Qed.

Example firstpos_a_then_b :
  firstpos positioned_a_then_b = [0].
Proof. reflexivity. Qed.

Example lastpos_a_then_b :
  lastpos positioned_a_then_b = [1].
Proof. reflexivity. Qed.

Example followpos_a_then_b :
  followpos positioned_a_then_b = [(0, [1])].
Proof. reflexivity. Qed.

Definition label_of_a_then_b (p : nat) : option bool :=
  match p with
  | 0 => Some true
  | 1 => Some false
  | _ => None
  end.

Definition bool_position_automaton :=
  build Bool.eqb label_of_a_then_b positioned_a_then_b.

Fixpoint nat_list_eqb (xs ys : list nat) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => Nat.eqb x y && nat_list_eqb xs' ys'
  | _, _ => false
  end.

Lemma nat_list_eqb_sound :
  forall xs ys, nat_list_eqb xs ys = true -> xs = ys.
Proof.
  induction xs as [| x xs IH]; destruct ys as [| y ys]; simpl; intros H;
    try discriminate; auto.
  apply andb_true_iff in H as [Hxy Htail].
  apply Nat.eqb_eq in Hxy.
  apply IH in Htail.
  subst. reflexivity.
Qed.

Lemma bool_eqb_sound :
  forall x y, Bool.eqb x y = true -> x = y.
Proof.
  intros [] []; simpl; intros H; try discriminate; reflexivity.
Qed.

Example a_then_b_self_equivb :
  equivb_with_fuel
    [true; false]
    bool_position_automaton
    bool_position_automaton
    nat_list_eqb
    nat_list_eqb
    10 = true.
Proof. reflexivity. Qed.

Example matches_a_then_b :
  matches a_then_b [true; false].
Proof.
  replace [true; false] with ([true] ++ [false]) by reflexivity.
  apply M_Cat.
  - apply M_Atom.
  - apply M_Atom.
Qed.

Example label_semantics_a_then_b :
  exists mw,
    symbols mw = [true; false] /\
    matches_marked (label a_then_b) mw.
Proof.
  apply label_semantics_preserved.
  apply matches_a_then_b.
Qed.

Example accepts_marked_a_then_b :
  accepts_marked positioned_a_then_b [(0, true); (1, false)].
Proof.
  unfold accepts_marked, positioned_a_then_b, a_then_b.
  simpl. repeat split; reflexivity.
Qed.

Example position_nfa_a_then_b_one_run :
  ambiguity_of_word
    (position_nfa Bool.eqb positioned_a_then_b)
    [true; false] = 1.
Proof. reflexivity. Qed.

Example position_nfa_a_then_b_no_eda_fuel_2 :
  edab_with_fuel
    2
    (finite_position_nfa [true; false] Bool.eqb positioned_a_then_b) = false.
Proof. reflexivity. Qed.

Definition ambiguous_a : regex bool :=
  Alt (Atom true) (Atom true).

Example position_nfa_ambiguous_a_two_runs :
  ambiguity_of_word
    (position_nfa Bool.eqb (label ambiguous_a))
    [true] = 2.
Proof. reflexivity. Qed.

Definition unit_eqb (_ _ : unit) : bool := true.

Lemma unit_eqb_sound :
  forall x y, unit_eqb x y = true -> x = y.
Proof.
  intros [] [] _. reflexivity.
Qed.

Lemma unit_eqb_complete :
  forall x y, x = y -> unit_eqb x y = true.
Proof.
  intros [] [] _. reflexivity.
Qed.

Definition duplicated_loop_nfa : @finite_nfa bool :=
  {|
    fnfa_base :=
      {|
        nfa_state := unit;
        nfa_start := [tt];
        nfa_final := fun _ => true;
        nfa_step := fun (_ : unit) (a : bool) => if a then [tt; tt] else []
      |};
    fnfa_states := [tt];
    fnfa_alphabet := [true];
    fnfa_state_eqb := unit_eqb;
    fnfa_state_eqb_sound := unit_eqb_sound;
    fnfa_state_eqb_complete := unit_eqb_complete
  |}.

Example duplicated_loop_word_has_two_runs :
  ambiguity_of_word duplicated_loop_nfa [true] = 2.
Proof. reflexivity. Qed.

Example duplicated_loop_edab :
  edab_with_fuel 1 duplicated_loop_nfa = true.
Proof. reflexivity. Qed.

Example duplicated_loop_eda :
  EDA duplicated_loop_nfa.
Proof.
  apply edab_with_fuel_sound with (fuel := 1).
  reflexivity.
Qed.

Definition nat_state_step (q : nat) (a : bool) : list nat :=
  if a then
    match q with
    | 0 => [0; 1]
    | 1 => [1]
    | _ => []
    end
  else [].

Lemma nat_eqb_complete :
  forall x y : nat, x = y -> Nat.eqb x y = true.
Proof.
  intros x y H. subst. apply Nat.eqb_refl.
Qed.

Lemma nat_eqb_sound :
  forall x y : nat, Nat.eqb x y = true -> x = y.
Proof.
  intros x y H. now apply Nat.eqb_eq.
Qed.

Definition ida_example_nfa : @finite_nfa bool :=
  {|
    fnfa_base :=
      {|
        nfa_state := nat;
        nfa_start := [0];
        nfa_final := fun q => Nat.leb q 1;
        nfa_step := nat_state_step
      |};
    fnfa_states := [0; 1];
    fnfa_alphabet := [true];
    fnfa_state_eqb := Nat.eqb;
    fnfa_state_eqb_sound := nat_eqb_sound;
    fnfa_state_eqb_complete := nat_eqb_complete
  |}.

Example ida_example_idab :
  idab_with_fuel 1 ida_example_nfa = true.
Proof. reflexivity. Qed.

Example ida_example_satisfies_ida :
  IDA ida_example_nfa.
Proof.
  apply idab_with_fuel_sound with (fuel := 1).
  reflexivity.
Qed.
