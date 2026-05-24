From Stdlib Require Import List Bool.
Import ListNotations.

From PositionAutomata Require Import PositionAutomaton.

(** A verified equivalence checker for deterministic finite automata.

    The checker is parameterized by a finite alphabet.  For position automata
    over character classes, this alphabet can later be instantiated with a
    finite partition of the relevant character domain. *)

Section Equivalence.
  Context {A : Type}.
  Context (alphabet : list A).
  Context (eqbA : A -> A -> bool).
  Context (eqbA_sound : forall x y, eqbA x y = true -> x = y).

  Context (m1 m2 : @automaton A).
  Context (eqb1 : state m1 -> state m1 -> bool).
  Context (eqb2 : state m2 -> state m2 -> bool).
  Context (eqb1_sound : forall x y, eqb1 x y = true -> x = y).
  Context (eqb2_sound : forall x y, eqb2 x y = true -> x = y).

  Definition pair_state : Type := (state m1 * state m2)%type.

  Definition pair_eqb (p q : pair_state) : bool :=
    eqb1 (fst p) (fst q) && eqb2 (snd p) (snd q).

  Definition pair_in (p : pair_state) (r : list pair_state) : bool :=
    existsb (pair_eqb p) r.

  Definition all_in_alphabet (w : list A) : bool :=
    forallb (fun a => existsb (eqbA a) alphabet) w.

  Fixpoint run (m : @automaton A) (s : state m) (w : list A) : state m :=
    match w with
    | [] => s
    | a :: w' => run m (step m s a) w'
    end.

  Definition accepts (m : @automaton A) (w : list A) : bool :=
    final m (run m (start m) w).

  Definition same_final (p : pair_state) : bool :=
    Bool.eqb (final m1 (fst p)) (final m2 (snd p)).

  Definition successor (p : pair_state) (a : A) : pair_state :=
    (step m1 (fst p) a, step m2 (snd p) a).

  Definition check_pair (r : list pair_state) (p : pair_state) : bool :=
    same_final p &&
    forallb (fun a => pair_in (successor p a) r) alphabet.

  Definition check_relation (r : list pair_state) : bool :=
    forallb (check_pair r) r.

  Definition start_pair : pair_state := (start m1, start m2).

  Definition equiv_certificate (r : list pair_state) : bool :=
    pair_in start_pair r && check_relation r.

  Definition add_pair (p : pair_state) (r : list pair_state) : list pair_state :=
    if pair_in p r then r else p :: r.

  Fixpoint add_fresh_pairs
      (ps seen todo : list pair_state) : list pair_state :=
    match ps with
    | [] => todo
    | p :: ps' =>
        let IsVisited := pair_in p seen || pair_in p todo in
        add_fresh_pairs ps' seen (if IsVisited then todo else p :: todo)
    end.

  Definition successors (p : pair_state) : list pair_state :=
    map (successor p) alphabet.

  Fixpoint explore
      (fuel : nat) (seen todo : list pair_state) : option (list pair_state) :=
    match fuel with
    | O => None
    | S fuel' =>
        match todo with
        | [] => Some seen
        | p :: todo' =>
            let seen' := add_pair p seen in
            let todo'' := add_fresh_pairs (successors p) seen' todo' in
            explore fuel' seen' todo''
        end
    end.

  Definition equivb_with_fuel (fuel : nat) : bool :=
    match explore fuel [] [start_pair] with
    | Some r => equiv_certificate r
    | None => false
    end.

  Lemma pair_eqb_true_eq :
    forall p q, pair_eqb p q = true -> p = q.
  Proof.
    intros [s1 s2] [t1 t2] H.
    unfold pair_eqb in H. simpl in H.
    apply andb_true_iff in H as [H1 H2].
    apply eqb1_sound in H1.
    apply eqb2_sound in H2.
    subst. reflexivity.
  Qed.

  Lemma pair_in_true_In :
    forall p r, pair_in p r = true -> In p r.
  Proof.
    intros p r H.
    unfold pair_in in H.
    apply existsb_exists in H as [q [Hin Heq]].
    apply pair_eqb_true_eq in Heq.
    subst. exact Hin.
  Qed.

  Lemma alphabet_member :
    forall a, existsb (eqbA a) alphabet = true -> In a alphabet.
  Proof.
    intros a H.
    apply existsb_exists in H as [b [Hin Heq]].
    apply eqbA_sound in Heq.
    subst. exact Hin.
  Qed.

  Lemma certificate_start :
    forall r,
      equiv_certificate r = true ->
      pair_in start_pair r = true.
  Proof.
    intros r H.
    unfold equiv_certificate in H.
    apply andb_true_iff in H as [H _].
    exact H.
  Qed.

  Lemma certificate_checks :
    forall r p,
      equiv_certificate r = true ->
      In p r ->
      check_pair r p = true.
  Proof.
    intros r p Hcert Hin.
    unfold equiv_certificate in Hcert.
    apply andb_true_iff in Hcert as [_ Hrel].
    unfold check_relation in Hrel.
    rewrite forallb_forall in Hrel.
    apply Hrel in Hin as Hcheck.
    exact Hcheck.
  Qed.

  Lemma checked_pair_same_final :
    forall r p,
      check_pair r p = true ->
      final m1 (fst p) = final m2 (snd p).
  Proof.
    intros r p H.
    unfold check_pair, same_final in H.
    apply andb_true_iff in H as [H _].
    destruct (final m1 (fst p)), (final m2 (snd p)); simpl in H;
      try discriminate; reflexivity.
  Qed.

  Lemma checked_pair_successor :
    forall r p a,
      check_pair r p = true ->
      In a alphabet ->
      pair_in (successor p a) r = true.
  Proof.
    intros r p a Hcheck Ha.
    unfold check_pair in Hcheck.
    apply andb_true_iff in Hcheck as [_ Hsucc].
    apply (proj1 (forallb_forall (fun a => pair_in (successor p a) r) alphabet)).
    exact Hsucc.
    exact Ha.
  Qed.

  Lemma certificate_run_from_pair :
    forall r w s1 s2,
      equiv_certificate r = true ->
      all_in_alphabet w = true ->
      pair_in (s1, s2) r = true ->
      pair_in (run m1 s1 w, run m2 s2 w) r = true.
  Proof.
    intros r w.
    induction w as [| a w IH]; simpl in *.
    - intros s1 s2 _ _ Hpair. exact Hpair.
    - intros s1 s2 Hcert Halph Hpair.
      apply andb_true_iff in Halph as [Ha Hw].
      pose proof pair_in_true_In _ _ Hpair as Hin.
      pose proof certificate_checks _ _ Hcert Hin as Hcheck.
      apply checked_pair_successor with (a := a) in Hcheck.
      + apply IH; auto.
      + apply alphabet_member. exact Ha.
  Qed.

  Lemma certificate_run_pair :
    forall r w,
      equiv_certificate r = true ->
      all_in_alphabet w = true ->
      pair_in (run m1 (start m1) w, run m2 (start m2) w) r = true.
  Proof.
    intros r w Hcert Halph.
    apply certificate_run_from_pair; auto.
    apply certificate_start. exact Hcert.
  Qed.

  Theorem equiv_certificate_sound :
    forall r w,
      equiv_certificate r = true ->
      all_in_alphabet w = true ->
      accepts m1 w = accepts m2 w.
  Proof.
    intros r w Hcert Halph.
    pose proof certificate_run_pair r w Hcert Halph as Hmem.
    pose proof pair_in_true_In _ _ Hmem as Hin.
    pose proof certificate_checks _ _ Hcert Hin as Hcheck.
    pose proof checked_pair_same_final _ _ Hcheck as Hfinal.
    unfold accepts. exact Hfinal.
  Qed.

  Theorem equivb_with_fuel_sound :
    forall fuel w,
      equivb_with_fuel fuel = true ->
      all_in_alphabet w = true ->
      accepts m1 w = accepts m2 w.
  Proof.
    intros fuel w Hequiv Halph.
    unfold equivb_with_fuel in Hequiv.
    destruct (explore fuel [] [start_pair]) as [r |] eqn:Hexplore;
      try discriminate.
    eapply equiv_certificate_sound; eauto.
  Qed.
End Equivalence.
