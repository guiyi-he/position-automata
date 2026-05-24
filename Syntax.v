From Stdlib Require Import List.
Import ListNotations.

(** Source regular expressions.

    The atoms in [regex] do not carry positions.  A separate numbering pass
    turns them into [positioned_regex], which is the syntax consumed by the
    position-automaton construction. *)

Inductive regex (A : Type) : Type :=
| Empty : regex A
| Eps : regex A
| Atom : A -> regex A
| Alt : regex A -> regex A -> regex A
| Cat : regex A -> regex A -> regex A
| Star : regex A -> regex A.

Arguments Empty {A}.
Arguments Eps {A}.
Arguments Atom {A} _.
Arguments Alt {A} _ _.
Arguments Cat {A} _ _.
Arguments Star {A} _.

Inductive positioned_regex (A : Type) : Type :=
| PEmpty : positioned_regex A
| PEps : positioned_regex A
| PAtom : nat -> A -> positioned_regex A
| PAlt : positioned_regex A -> positioned_regex A -> positioned_regex A
| PCat : positioned_regex A -> positioned_regex A -> positioned_regex A
| PStar : positioned_regex A -> positioned_regex A.

Arguments PEmpty {A}.
Arguments PEps {A}.
Arguments PAtom {A} _ _.
Arguments PAlt {A} _ _.
Arguments PCat {A} _ _.
Arguments PStar {A} _.

(* a1b2* ----> {1,2} *)

Fixpoint positions {A : Type} (r : positioned_regex A) : list nat :=
  match r with
  | PEmpty | PEps => []
  | PAtom p _ => [p]
  | PAlt r1 r2 | PCat r1 r2 => positions r1 ++ positions r2
  | PStar r' => positions r'
  end.

Fixpoint label_from {A : Type} (fresh : nat) (r : regex A)
  : positioned_regex A * nat :=
  match r with
  | Empty => (PEmpty, fresh)
  | Eps => (PEps, fresh)
  | Atom a => (PAtom fresh a, S fresh)
  | Alt r1 r2 =>
      let (r1', fresh1) := label_from fresh r1 in
      let (r2', fresh2) := label_from fresh1 r2 in
      (PAlt r1' r2', fresh2)
  | Cat r1 r2 =>
      let (r1', fresh1) := label_from fresh r1 in
      let (r2', fresh2) := label_from fresh1 r2 in
      (PCat r1' r2', fresh2)
  | Star r' =>
      let (r'', fresh') := label_from fresh r' in
      (PStar r'', fresh')
  end.

Definition label {A : Type} (r : regex A) : positioned_regex A :=
  fst (label_from 0 r).

Definition next_position {A : Type} (r : regex A) : nat :=
  snd (label_from 0 r).
