Require Import List Bool Arith.
Import ListNotations.

From PositionAutomata Require Import Syntax PositionAutomaton Equivalence KleeneSemantics.

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
