From Stdlib Require Import List Arith Lia.
Import ListNotations.

(** Lightweight finite sets represented as lists.

    The development deliberately keeps this small: the construction functions
    are useful even before uniqueness invariants are added.  Later proofs can
    refine [set] with [NoDup] if that becomes convenient. *)

Definition set := list nat.

Fixpoint mem (x : nat) (xs : set) : bool :=
  match xs with
  | [] => false
  | y :: ys => Nat.eqb x y || mem x ys
  end.

Definition add (x : nat) (xs : set) : set :=
  if mem x xs then xs else x :: xs.

Fixpoint union (xs ys : set) : set :=
  match xs with
  | [] => ys
  | x :: xs' => add x (union xs' ys)
  end.

Fixpoint subset (xs ys : set) : bool :=
  match xs with
  | [] => true
  | x :: xs' => mem x ys && subset xs' ys
  end.

Lemma mem_add_eq :
  forall x xs, mem x (add x xs) = true.
Proof.
  intros x xs. unfold add.
  destruct (mem x xs) eqn:H; simpl; auto.
  rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma mem_union_left :
  forall x xs ys, mem x xs = true -> mem x (union xs ys) = true.
Proof.
  intros x xs ys.
  induction xs as [| y xs IH]; simpl; intros H; try discriminate.
  apply Bool.orb_true_iff in H as [H | H].
  - apply Nat.eqb_eq in H. subst. apply mem_add_eq.
  - unfold add.
    destruct (mem y (union xs ys)) eqn:Hy; simpl.
    + apply IH. exact H.
    + destruct (Nat.eqb x y) eqn:Hxy.
      * reflexivity.
      * apply IH. exact H.
Qed.

Lemma mem_union_right :
  forall x xs ys, mem x ys = true -> mem x (union xs ys) = true.
Proof.
  intros x xs ys.
  induction xs as [| y xs IH]; simpl; intros H; auto.
  unfold add.
  destruct (mem y (union xs ys)) eqn:Hy; simpl; auto.
  destruct (Nat.eqb x y) eqn:Hxy; auto.
Qed.
