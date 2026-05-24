From Stdlib Require Import List Arith Bool Lia.
Import ListNotations.

From PositionAutomata Require Import Sets Syntax PositionAutomaton.

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

Lemma sum_nats_pos_In :
  forall xs,
    0 < sum_nats xs ->
    exists x, In x xs /\ 0 < x.
Proof.
  induction xs as [| x xs IH]; simpl; intros Hpos.
  - lia.
  - destruct x as [| x'].
    + destruct (IH Hpos) as [y [Hy Hlt]].
      exists y. split; simpl; auto.
    + exists (S x'). split; simpl; auto; lia.
Qed.

Lemma sum_map_pos_In :
  forall {B : Type} (f : B -> nat) xs,
    0 < sum_nats (map f xs) ->
    exists x, In x xs /\ 0 < f x.
Proof.
  intros B f xs Hpos.
  apply sum_nats_pos_In in Hpos as [n [Hin Hn]].
  apply in_map_iff in Hin as [x [Hx Hin]].
  subst.
  exists x. split; assumption.
Qed.

Section NFA.
  Context {A : Type}.

  Record nfa : Type := {
    nfa_state : Type;
    nfa_start : list nfa_state;
    nfa_final : nfa_state -> bool;
    nfa_step : nfa_state -> A -> list nfa_state
  }.

  Record finite_nfa : Type := {
    fnfa_base :> nfa;
    fnfa_states : list (nfa_state fnfa_base);
    fnfa_alphabet : list A;
    fnfa_state_eqb : nfa_state fnfa_base -> nfa_state fnfa_base -> bool;
    fnfa_state_eqb_sound :
      forall x y, fnfa_state_eqb x y = true -> x = y;
    fnfa_state_eqb_complete :
      forall x y, x = y -> fnfa_state_eqb x y = true
  }.

  Inductive path_from (m : nfa)
      : nfa_state m -> list A -> nfa_state m -> Prop :=
  | Path_nil :
      forall q,
        path_from m q [] q
  | Path_cons :
      forall q a q' w q'',
        In q' (nfa_step m q a) ->
        path_from m q' w q'' ->
        path_from m q (a :: w) q''.

  Definition delta_star (m : nfa) : nfa_state m -> list A -> nfa_state m -> Prop :=
    path_from m.

  Definition accepting_path (m : nfa) (w : list A) : Prop :=
    exists q0 qf,
      In q0 (nfa_start m) /\
      path_from m q0 w qf /\
      nfa_final m qf = true.

  Definition useful_state (m : nfa) (q : nfa_state m) : Prop :=
    exists q0 qf w1 w2,
      In q0 (nfa_start m) /\
      path_from m q0 w1 q /\
      path_from m q w2 qf /\
      nfa_final m qf = true.

  Definition connected (m : nfa) (p q : nfa_state m) : Prop :=
    exists u v,
      path_from m p u q /\ path_from m q v p.

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

  Definition infinitely_ambiguous (m : nfa) : Prop :=
    forall k, exists w, k <= ambiguity_of_word m w.

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

  Fixpoint runs_between
      (m : finite_nfa)
      (q : nfa_state (fnfa_base m))
      (w : list A)
      (r : nfa_state (fnfa_base m)) : nat :=
    match w with
    | [] => if fnfa_state_eqb m q r then 1 else 0
    | a :: w' =>
        sum_nats
          (map
             (fun q' => runs_between m q' w' r)
             (nfa_step (fnfa_base m) q a))
    end.

  Definition da_from_to := runs_between.

  Definition start_runs_to
      (m : finite_nfa)
      (w : list A)
      (q : nfa_state (fnfa_base m)) : nat :=
    sum_nats
      (map
         (fun q0 => runs_between m q0 w q)
         (nfa_start (fnfa_base m))).

  Lemma runs_between_positive_path :
    forall (m : finite_nfa) q w r,
      0 < runs_between m q w r ->
      path_from (fnfa_base m) q w r.
  Proof.
    intros m q w.
    generalize dependent q.
    induction w as [| a w IH]; intros q r Hpos; simpl in Hpos.
    - destruct (fnfa_state_eqb m q r) eqn:Heq; try lia.
      apply fnfa_state_eqb_sound in Heq. subst.
      constructor.
    - apply sum_map_pos_In in Hpos as [q' [Hin Hpos]].
      eapply Path_cons; eauto.
  Qed.

  Lemma start_runs_to_positive_path :
    forall (m : finite_nfa) w q,
      0 < start_runs_to m w q ->
      exists q0,
        In q0 (nfa_start (fnfa_base m)) /\
        path_from (fnfa_base m) q0 w q.
  Proof.
    intros m w q Hpos.
    unfold start_runs_to in Hpos.
    apply sum_map_pos_In in Hpos as [q0 [Hin Hpos]].
    exists q0. split; auto.
    now apply runs_between_positive_path.
  Qed.

  Lemma accepting_runs_from_positive_path :
    forall (m : nfa) q w,
      0 < accepting_runs_from m q w ->
      exists qf,
        path_from m q w qf /\
        nfa_final m qf = true.
  Proof.
    intros m q w.
    revert q.
    induction w as [| a w IH]; intros q Hpos; simpl in Hpos.
    - destruct (nfa_final m q) eqn:Hfinal; try lia.
      exists q. split; constructor || assumption.
    - apply sum_map_pos_In in Hpos as [q' [Hin Hpos]].
      destruct (IH q' Hpos) as [qf [Hpath Hfinal]].
      exists qf. split; auto.
      eapply Path_cons; eauto.
  Qed.

  Lemma useful_state_from_positive_tests :
    forall (m : finite_nfa) q w_in w_out,
      0 < start_runs_to m w_in q ->
      0 < accepting_runs_from (fnfa_base m) q w_out ->
      useful_state (fnfa_base m) q.
  Proof.
    intros m q w_in w_out Hin Hout.
    destruct (start_runs_to_positive_path m w_in q Hin) as [q0 [Hstart Hpath_in]].
    destruct (accepting_runs_from_positive_path (fnfa_base m) q w_out Hout)
      as [qf [Hpath_out Hfinal]].
    unfold useful_state.
    exists q0, qf, w_in, w_out.
    repeat split; assumption.
  Qed.

  Definition option_nat_eqb (x y : option nat) : bool :=
    match x, y with
    | None, None => true
    | Some x', Some y' => Nat.eqb x' y'
    | _, _ => false
    end.

  Lemma option_nat_eqb_sound :
    forall x y, option_nat_eqb x y = true -> x = y.
  Proof.
    intros [x|] [y|]; simpl; intros H; try discriminate; auto.
    apply Nat.eqb_eq in H. subst. reflexivity.
  Qed.

  Lemma option_nat_eqb_complete :
    forall x y, x = y -> option_nat_eqb x y = true.
  Proof.
    intros x y H. subst.
    destruct y as [y|]; simpl; auto.
    apply Nat.eqb_refl.
  Qed.

  Definition position_nfa_state : Type := option nat.

  Definition matching_positions
      (label_matches : A -> A -> bool)
      (lbl : symbol_at)
      (ps : list nat)
      (a : A) : list position_nfa_state :=
    fold_right
      (fun p acc =>
         match lbl p with
         | Some b =>
             if label_matches b a then Some p :: acc else acc
         | None => acc
         end)
      []
      ps.

  Definition position_nfa_step
      (label_matches : A -> A -> bool)
      (r : positioned_regex A)
      (s : position_nfa_state)
      (a : A) : list position_nfa_state :=
    let lbl := label_of r in
    match s with
    | None => matching_positions label_matches lbl (firstpos r) a
    | Some p => matching_positions label_matches lbl (lookup_follow p (followpos r)) a
    end.

  Definition position_nfa_final
      (r : positioned_regex A)
      (s : position_nfa_state) : bool :=
    match s with
    | None => nullable r
    | Some p => mem p (lastpos r)
    end.

  Definition position_nfa
      (label_matches : A -> A -> bool)
      (r : positioned_regex A) : nfa :=
    {|
      nfa_state := position_nfa_state;
      nfa_start := [None];
      nfa_final := position_nfa_final r;
      nfa_step := position_nfa_step label_matches r
    |}.

  Definition finite_position_nfa
      (alphabet : list A)
      (label_matches : A -> A -> bool)
      (r : positioned_regex A) : finite_nfa :=
    {|
      fnfa_base := position_nfa label_matches r;
      fnfa_states := None :: map Some (positions r);
      fnfa_alphabet := alphabet;
      fnfa_state_eqb := option_nat_eqb;
      fnfa_state_eqb_sound := option_nat_eqb_sound;
      fnfa_state_eqb_complete := option_nat_eqb_complete
    |}.

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
