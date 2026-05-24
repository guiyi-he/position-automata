From Stdlib Require Import List Bool Arith Lia.
Import ListNotations.

From PositionAutomata Require Import DegreeofAmbiguity.

(** Weber-Seidl style ambiguity witnesses.

    This file intentionally starts with the ReDoS-relevant, executable core:
    fuel-bounded search procedures for IDA and EDA witnesses, together with
    soundness theorems into the Prop-level criteria.  The complete converse
    directions from Weber and Seidl Section 3/4 are left as future theorem
    targets rather than assumed as axioms. *)

Section InfiniteAmbiguity.
  Context {A : Type}.

  Definition finite_state (m : @finite_nfa A) : Type :=
    nfa_state (fnfa_base m).

  Definition finite_delta_star
      (m : @finite_nfa A)
      (p : finite_state m)
      (w : list A)
      (q : finite_state m) : Prop :=
    path_from (fnfa_base m) p w q.

  Definition finite_useful
      (m : @finite_nfa A)
      (q : finite_state m) : Prop :=
    useful_state (fnfa_base m) q.

  Definition IDA (m : @finite_nfa A) : Prop :=
    exists p q v,
      p <> q /\
      finite_useful m p /\
      finite_useful m q /\
      finite_delta_star m p v p /\
      finite_delta_star m p v q /\
      finite_delta_star m q v q.

  Definition EDA (m : @finite_nfa A) : Prop :=
    exists q v,
      finite_useful m q /\
      finite_delta_star m q v q /\
      2 <= da_from_to m q v q.

  Definition IDA_d (m : @finite_nfa A) (d : nat) : Prop :=
    exists qs vs,
      length qs = d /\
      length vs = d /\
      Forall
        (fun qv =>
           let '(q, v) := qv in
           finite_useful m q /\
           finite_delta_star m q v q /\
           2 <= da_from_to m q v q)
        (combine qs vs).

  Definition has_exponential_pump := EDA.

  Fixpoint words_upto (alphabet : list A) (fuel : nat) : list (list A) :=
    match fuel with
    | O => [[]]
    | S fuel' =>
        words_upto alphabet fuel' ++ words_of_length alphabet (S fuel')
    end.

  Definition pathb
      (m : @finite_nfa A)
      (p : finite_state m)
      (w : list A)
      (q : finite_state m) : bool :=
    0 <? da_from_to m p w q.

  Definition usefulb_with_fuel
      (fuel : nat)
      (m : @finite_nfa A)
      (q : finite_state m) : bool :=
    existsb
      (fun w => 0 <? start_runs_to m w q)
      (words_upto (fnfa_alphabet m) fuel)
    &&
    existsb
      (fun w => 0 <? accepting_runs_from (fnfa_base m) q w)
      (words_upto (fnfa_alphabet m) fuel).

  Definition eda_stateb
      (fuel : nat)
      (m : @finite_nfa A)
      (q : finite_state m) : bool :=
    usefulb_with_fuel fuel m q
    &&
    existsb
      (fun v => 1 <? da_from_to m q v q)
      (words_upto (fnfa_alphabet m) fuel).

  Definition edab_with_fuel (fuel : nat) (m : @finite_nfa A) : bool :=
    existsb (eda_stateb fuel m) (fnfa_states m).

  Definition idab_pairb
      (fuel : nat)
      (m : @finite_nfa A)
      (p q : finite_state m) : bool :=
    negb (fnfa_state_eqb m p q)
    &&
    usefulb_with_fuel fuel m p
    &&
    usefulb_with_fuel fuel m q
    &&
    existsb
      (fun v =>
         pathb m p v p && pathb m p v q && pathb m q v q)
      (words_upto (fnfa_alphabet m) fuel).

  Definition idab_with_fuel (fuel : nat) (m : @finite_nfa A) : bool :=
    existsb
      (fun p => existsb (idab_pairb fuel m p) (fnfa_states m))
      (fnfa_states m).

  Lemma pathb_sound :
    forall (m : @finite_nfa A) p w q,
      pathb m p w q = true ->
      finite_delta_star m p w q.
  Proof.
    intros m p w q H.
    unfold pathb in H.
    apply Nat.ltb_lt in H.
    now apply runs_between_positive_path.
  Qed.

  Lemma usefulb_with_fuel_sound :
    forall fuel (m : @finite_nfa A) q,
      usefulb_with_fuel fuel m q = true ->
      finite_useful m q.
  Proof.
    intros fuel m q H.
    unfold usefulb_with_fuel in H.
    apply andb_true_iff in H as [Hin Hout].
    apply existsb_exists in Hin as [w_in [_ Hin]].
    apply existsb_exists in Hout as [w_out [_ Hout]].
    apply Nat.ltb_lt in Hin.
    apply Nat.ltb_lt in Hout.
    eapply useful_state_from_positive_tests; eauto.
  Qed.

  Lemma eda_stateb_sound :
    forall fuel (m : @finite_nfa A) q,
      eda_stateb fuel m q = true ->
      exists v,
        finite_useful m q /\
        finite_delta_star m q v q /\
        2 <= da_from_to m q v q.
  Proof.
    intros fuel m q H.
    unfold eda_stateb in H.
    apply andb_true_iff in H as [Huseful Hloop].
    apply existsb_exists in Hloop as [v [_ Hv]].
    apply Nat.ltb_lt in Hv.
    exists v.
    repeat split.
    - now apply usefulb_with_fuel_sound with (fuel := fuel).
    - unfold da_from_to in Hv.
      apply runs_between_positive_path. lia.
    - lia.
  Qed.

  Theorem edab_with_fuel_sound :
    forall fuel (m : @finite_nfa A),
      edab_with_fuel fuel m = true ->
      EDA m.
  Proof.
    intros fuel m H.
    unfold edab_with_fuel in H.
    apply existsb_exists in H as [q [_ Hq]].
    destruct (eda_stateb_sound fuel m q Hq) as [v [Huseful [Hloop Hcount]]].
    exists q, v.
    repeat split; assumption.
  Qed.

  Theorem edab_with_fuel_has_exponential_pump :
    forall fuel (m : @finite_nfa A),
      edab_with_fuel fuel m = true ->
      has_exponential_pump m.
  Proof.
    intros fuel m H.
    now apply edab_with_fuel_sound in H.
  Qed.

  Lemma idab_pairb_sound :
    forall fuel (m : @finite_nfa A) p q,
      idab_pairb fuel m p q = true ->
      exists v,
        p <> q /\
        finite_useful m p /\
        finite_useful m q /\
        finite_delta_star m p v p /\
        finite_delta_star m p v q /\
        finite_delta_star m q v q.
  Proof.
    intros fuel m p q H.
    unfold idab_pairb in H.
    apply andb_true_iff in H as [Hleft Hv].
    apply andb_true_iff in Hleft as [Hleft Huseful_q].
    apply andb_true_iff in Hleft as [Hneq Huseful_p].
    apply existsb_exists in Hv as [v [_ Hv]].
    apply andb_true_iff in Hv as [Hleft Hqq].
    apply andb_true_iff in Hleft as [Hpp Hpq].
    exists v.
    repeat split.
    - intros Heq. subst.
      pose proof (fnfa_state_eqb_complete m q q eq_refl) as Hrefl.
      rewrite Hrefl in Hneq. discriminate.
    - now apply usefulb_with_fuel_sound with (fuel := fuel).
    - now apply usefulb_with_fuel_sound with (fuel := fuel).
    - now apply pathb_sound.
    - now apply pathb_sound.
    - now apply pathb_sound.
  Qed.

  Theorem idab_with_fuel_sound :
    forall fuel (m : @finite_nfa A),
      idab_with_fuel fuel m = true ->
      IDA m.
  Proof.
    intros fuel m H.
    unfold idab_with_fuel in H.
    apply existsb_exists in H as [p [_ Hp]].
    apply existsb_exists in Hp as [q [_ Hq]].
    destruct (idab_pairb_sound fuel m p q Hq)
      as [v [Hneq [Hup [Huq [Hpp [Hpq Hqq]]]]]].
    exists p, q, v.
    repeat split; assumption.
  Qed.
End InfiniteAmbiguity.
