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

  Definition finite_state_eq_dec
      (m : @finite_nfa A)
      (p q : finite_state m) : {p = q} + {p <> q}.
  Proof.
    destruct (fnfa_state_eqb m p q) eqn:Heq.
    - left. now apply fnfa_state_eqb_sound.
    - right. intros Hpq.
      rewrite (fnfa_state_eqb_complete m p q Hpq) in Heq.
      discriminate.
  Defined.

  Definition nodup_finite_states (m : @finite_nfa A) : list (finite_state m) :=
    nodup (finite_state_eq_dec m) (fnfa_states m).

  Lemma nodup_finite_states_NoDup :
    forall (m : @finite_nfa A),
      NoDup (nodup_finite_states m).
  Proof.
    intros m.
    unfold nodup_finite_states.
    apply NoDup_nodup.
  Qed.

  Lemma nodup_finite_states_In :
    forall (m : @finite_nfa A) q,
      In q (nodup_finite_states m) <-> In q (fnfa_states m).
  Proof.
    intros m q.
    unfold nodup_finite_states.
    apply nodup_In.
  Qed.

  Definition finite_state_payloads (m : @finite_nfa A) : list (finite_state m) :=
    nodup_finite_states m.

  Lemma finite_state_payloads_NoDup :
    forall (m : @finite_nfa A),
      NoDup (finite_state_payloads m).
  Proof.
    apply nodup_finite_states_NoDup.
  Qed.

  Lemma finite_state_payloads_length_le :
    forall (m : @finite_nfa A),
      length (finite_state_payloads m) <= length (fnfa_states m).
  Proof.
    intros m.
    unfold finite_state_payloads, nodup_finite_states.
    induction (fnfa_states m) as [| q qs IH]; simpl.
    - lia.
    - destruct (in_dec (finite_state_eq_dec m) q qs); simpl; lia.
  Qed.

  Lemma finite_state_payloads_In :
    forall (m : @finite_nfa A) q,
      In q (finite_state_payloads m) <-> In q (fnfa_states m).
  Proof.
    apply nodup_finite_states_In.
  Qed.

  Definition finite_state_pair_payloads
      (m : @finite_nfa A) : list (finite_state m * finite_state m) :=
    product_codes (finite_state_payloads m) (finite_state_payloads m).

  Lemma finite_state_pair_payloads_NoDup :
    forall (m : @finite_nfa A),
      NoDup (finite_state_pair_payloads m).
  Proof.
    intros m.
    unfold finite_state_pair_payloads.
    apply product_codes_NoDup;
      apply finite_state_payloads_NoDup.
  Qed.

  Lemma finite_state_pair_payloads_length_le :
    forall (m : @finite_nfa A),
      length (finite_state_pair_payloads m) <=
        length (fnfa_states m) * length (fnfa_states m).
  Proof.
    intros m.
    unfold finite_state_pair_payloads.
    rewrite product_codes_length.
    pose proof (finite_state_payloads_length_le m) as Hle.
    nia.
  Qed.

  Lemma finite_state_pair_payloads_In :
    forall (m : @finite_nfa A) p q,
      In p (fnfa_states m) ->
      In q (fnfa_states m) ->
      In (p, q) (finite_state_pair_payloads m).
  Proof.
    intros m p q Hp Hq.
    unfold finite_state_pair_payloads.
    apply product_codes_In;
      apply finite_state_payloads_In;
      assumption.
  Qed.

  Fixpoint index_of {B : Type}
      (eq_dec : forall x y : B, {x = y} + {x <> y})
      (x : B)
      (xs : list B) : nat :=
    match xs with
    | [] => 0
    | y :: ys =>
        if eq_dec x y then 0 else S (index_of eq_dec x ys)
    end.

  Lemma index_of_lt :
    forall (B : Type)
      (eq_dec : forall x y : B, {x = y} + {x <> y})
      (x : B) xs,
      In x xs ->
      index_of eq_dec x xs < length xs.
  Proof.
    intros B eq_dec x xs.
    induction xs as [| y ys IH]; intros Hin; simpl in *.
    - contradiction.
    - destruct (eq_dec x y) as [Heq | Hneq].
      + lia.
      + destruct Hin as [Hin | Hin].
        * symmetry in Hin. contradiction.
        * specialize (IH Hin). lia.
  Qed.

  Lemma nth_error_index_of :
    forall (B : Type)
      (eq_dec : forall x y : B, {x = y} + {x <> y})
      (x : B) xs,
      In x xs ->
      nth_error xs (index_of eq_dec x xs) = Some x.
  Proof.
    intros B eq_dec x xs.
    induction xs as [| y ys IH]; intros Hin; simpl in *.
    - contradiction.
    - destruct (eq_dec x y) as [Heq | Hneq].
      + now subst y.
      + destruct Hin as [Hin | Hin].
        * symmetry in Hin. contradiction.
        * now apply IH.
  Qed.

  Lemma index_of_NoDup_eq :
    forall (B : Type)
      (eq_dec : forall x y : B, {x = y} + {x <> y})
      xs x y,
      NoDup xs ->
      In x xs ->
      In y xs ->
      index_of eq_dec x xs = index_of eq_dec y xs ->
      x = y.
  Proof.
    intros B eq_dec xs.
    induction xs as [| z zs IH]; intros x y Hnodup Hx Hy Hidx;
      simpl in *; try contradiction.
    inversion Hnodup as [| ? ? Hz_notin Hnodup_tail]; subst.
    destruct (eq_dec x z) as [Hxz | Hxz];
      destruct (eq_dec y z) as [Hyz | Hyz]; subst; auto.
    - discriminate.
    - discriminate.
    - destruct Hx as [Hx | Hx]; [subst; contradiction |].
      destruct Hy as [Hy | Hy]; [subst; contradiction |].
      injection Hidx as Hidx_tail.
      eapply IH; eauto.
  Qed.

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

  Lemma finite_useful_from_accepting_trace_nth :
    forall (m : @finite_nfa A) q0 w qf trace pos mid,
      In q0 (nfa_start (fnfa_base m)) ->
      run_trace_from (fnfa_base m) q0 w qf trace ->
      nfa_final (fnfa_base m) qf = true ->
      nth_error trace pos = Some mid ->
      finite_useful m mid.
  Proof.
    intros m q0 w qf trace pos mid Hstart Htrace Hfinal Hnth.
    unfold finite_useful.
    eapply useful_state_from_accepting_trace_nth; eauto.
  Qed.

  Definition IDA_pair
      (m : @finite_nfa A)
      (p q : finite_state m)
      (v : list A) : Prop :=
      p <> q /\
      finite_useful m p /\
      finite_useful m q /\
      finite_delta_star m p v p /\
      finite_delta_star m p v q /\
      finite_delta_star m q v q.

  Definition IDA (m : @finite_nfa A) : Prop :=
    exists p q v, IDA_pair m p q v.

  Definition EDA (m : @finite_nfa A) : Prop :=
    exists q v,
      finite_useful m q /\
      finite_delta_star m q v q /\
      2 <= da_from_to m q v q.

  Inductive IDA_chain (m : @finite_nfa A)
      : nat -> finite_state m -> finite_state m -> Prop :=
  | IDA_chain_one :
      forall r s v,
        IDA_pair m r s v ->
        IDA_chain m 1 r s
  | IDA_chain_cons :
      forall d r s v u r' s',
        IDA_pair m r s v ->
        finite_delta_star m s u r' ->
        IDA_chain m d r' s' ->
        IDA_chain m (S d) r s'.

  Definition IDA_d (m : @finite_nfa A) (d : nat) : Prop :=
    match d with
    | O => True
    | S _ => exists r s, IDA_chain m d r s
    end.

  Lemma IDA_chain_zero_false :
    forall (m : @finite_nfa A) r s,
      IDA_chain m 0 r s -> False.
  Proof.
    intros m r s H. inversion H.
  Qed.

  Lemma IDA_d_one_iff_IDA :
    forall (m : @finite_nfa A),
      IDA_d m 1 <-> IDA m.
  Proof.
    intros m. split.
    - intros [r [s Hchain]].
      inversion Hchain; subst.
      + exists r, s, v. exact H.
      + exfalso. eauto using IDA_chain_zero_false.
    - intros [r [s [v Hpair]]].
      exists r, s. now apply IDA_chain_one with (v := v).
  Qed.

  Lemma IDA_pair_connector_chain :
    forall (m : @finite_nfa A) p q v u d,
      IDA_pair m p q v ->
      finite_delta_star m q u p ->
      IDA_chain m (S d) p q.
  Proof.
    intros m p q v u d Hpair Hconnector.
    induction d as [| d IH].
    - now apply IDA_chain_one with (v := v).
    - eapply IDA_chain_cons
        with (s := q) (v := v) (u := u) (r' := p).
      + exact Hpair.
      + exact Hconnector.
      + exact IH.
  Qed.

  Definition has_exponential_pump := EDA.

  Definition exponentially_ambiguous (m : @nfa A) : Prop :=
    forall n, exists w, Nat.pow 2 n <= ambiguity_of_word m w.

  Fixpoint repeat_word (w : list A) (n : nat) : list A :=
    match n with
    | O => []
    | S n' => w ++ repeat_word w n'
    end.

  Lemma runs_between_repeat_word_ge_pow :
    forall (m : @finite_nfa A) q v n,
      2 <= da_from_to m q v q ->
      Nat.pow 2 n <= da_from_to m q (repeat_word v n) q.
  Proof.
    intros m q v n Hloop.
    induction n as [| n IH]; simpl.
    - unfold da_from_to. simpl.
      rewrite (fnfa_state_eqb_complete m q q eq_refl). lia.
    - eapply Nat.le_trans with
        (m := da_from_to m q v q *
          da_from_to m q (repeat_word v n) q).
      + nia.
      + apply runs_between_app_ge.
  Qed.

  Lemma runs_between_repeat_loop_positive :
    forall (m : @finite_nfa A) q v n,
      finite_delta_star m q v q ->
      0 < da_from_to m q (repeat_word v n) q.
  Proof.
    intros m q v n Hloop.
    induction n as [| n IH]; simpl.
    - unfold da_from_to. simpl.
      rewrite (fnfa_state_eqb_complete m q q eq_refl). lia.
    - pose proof (path_runs_between_positive m q v q Hloop) as Hv.
      pose proof
        (runs_between_app_ge m q v q (repeat_word v n) q)
        as Happ.
      unfold da_from_to in *. lia.
  Qed.

  Lemma IDA_pair_repeat_runs_lower :
    forall (m : @finite_nfa A) p q v n,
      IDA_pair m p q v ->
      n <= da_from_to m p (repeat_word v (S n)) q.
  Proof.
    intros m p q v n Hpair.
    destruct Hpair as [Hneq [_ [_ [Hpp [Hpq Hqq]]]]].
    induction n as [| n IH].
    - lia.
    - simpl.
      pose proof (path_runs_between_positive m p v p Hpp) as Hpp_pos.
      pose proof (path_runs_between_positive m p v q Hpq) as Hpq_pos.
      pose proof
        (runs_between_repeat_loop_positive m q v (S n) Hqq)
        as Hqq_rep_pos.
      pose proof
        (runs_between_app_ge_two
           m p v p q (repeat_word v (S n)) q Hneq)
        as Htwo.
      eapply Nat.le_trans with
        (m :=
          runs_between m p v p *
            runs_between m p (repeat_word v (S n)) q +
          runs_between m p v q *
            runs_between m q (repeat_word v (S n)) q).
      + unfold da_from_to in *. nia.
      + exact Htwo.
  Qed.

  Lemma IDA_pair_left_useful :
    forall (m : @finite_nfa A) p q v,
      IDA_pair m p q v -> finite_useful m p.
  Proof.
    intros m p q v Hpair.
    destruct Hpair as [_ [Hp _]]. exact Hp.
  Qed.

  Lemma IDA_pair_right_useful :
    forall (m : @finite_nfa A) p q v,
      IDA_pair m p q v -> finite_useful m q.
  Proof.
    intros m p q v Hpair.
    destruct Hpair as [_ [_ [Hq _]]]. exact Hq.
  Qed.

  Lemma IDA_chain_endpoints_useful :
    forall (m : @finite_nfa A) d r s,
      IDA_chain m d r s ->
      finite_useful m r /\ finite_useful m s.
  Proof.
    intros m d r s Hchain.
    induction Hchain.
    - split.
      + eapply IDA_pair_left_useful; eauto.
      + eapply IDA_pair_right_useful; eauto.
    - destruct IHHchain as [_ Hlast].
      split.
      + eapply IDA_pair_left_useful; eauto.
      + exact Hlast.
  Qed.

  Lemma IDA_chain_runs_between_lower :
    forall (m : @finite_nfa A) d r s,
      IDA_chain m d r s ->
      forall n, exists w,
        Nat.pow n d <= da_from_to m r w s.
  Proof.
    intros m d r s Hchain.
    induction Hchain; intros n.
    - exists (repeat_word v (S n)).
      simpl.
      pose proof (IDA_pair_repeat_runs_lower m r s v n H) as Hlower.
      replace (n * 1) with n by lia.
      exact Hlower.
    - destruct (IHHchain n) as [wtail Htail].
      exists (repeat_word v (S n) ++ u ++ wtail).
      pose proof (IDA_pair_repeat_runs_lower m r s v n H) as Hhead.
      pose proof (path_runs_between_positive m s u r' H0) as Hconnector.
      pose proof (runs_between_app_ge m s u r' wtail s') as Htail_app.
      pose proof
        (runs_between_app_ge
           m r (repeat_word v (S n)) s (u ++ wtail) s')
        as Hall.
      change (n * Nat.pow n d <=
        da_from_to m r (repeat_word v (S n) ++ u ++ wtail) s').
      unfold da_from_to in *.
      set (Rhead := runs_between m r (repeat_word v (S n)) s) in *.
      set (Rconnector := runs_between m s u r') in *.
      set (Rtail := runs_between m r' wtail s') in *.
      set (Rafter_connector := runs_between m s (u ++ wtail) s') in *.
      set (Rall :=
        runs_between m r (repeat_word v (S n) ++ u ++ wtail) s') in *.
      assert (Htail_lower : Nat.pow n d <= Rafter_connector).
      {
        eapply Nat.le_trans with (m := Rconnector * Rtail).
        - nia.
        - exact Htail_app.
      }
      eapply Nat.le_trans with (m := Rhead * Rafter_connector).
      + nia.
      + exact Hall.
  Qed.

  Definition polynomial_growth_lower_bound (m : @nfa A) (d : nat) : Prop :=
    forall n, exists w, Nat.pow n d <= ambiguity_of_word m w.

  Definition degree_at_least := polynomial_growth_lower_bound.

  Theorem IDA_d_polynomial_growth_lower_bound :
    forall (m : @finite_nfa A) d,
      IDA_d m (S d) ->
      polynomial_growth_lower_bound (fnfa_base m) (S d).
  Proof.
    intros m d Hid n.
    destruct Hid as [r [s Hchain]].
    destruct (IDA_chain_runs_between_lower m (S d) r s Hchain n)
      as [wmid Hmid].
    destruct (IDA_chain_endpoints_useful m (S d) r s Hchain)
      as [Huseful_r Huseful_s].
    destruct Huseful_r as [q0 [qf0 [w_in [w_out0 Hr]]]].
    destruct Hr as [Hstart [Hpath_in Hr_out]].
    destruct Huseful_s as [q0s [qf [w_ins [w_out Hs]]]].
    destruct Hs as [Hstart_s [Hpath_in_s [Hpath_out Hfinal]]].
    exists (w_in ++ wmid ++ w_out).
    pose proof (path_runs_between_positive m q0 w_in r Hpath_in)
      as Hin_pos.
    pose proof
      (path_accepting_runs_from_positive
         (fnfa_base m) s w_out qf Hpath_out Hfinal)
      as Hout_pos.
    pose proof (accepting_runs_from_app_ge m r wmid s w_out)
      as Hmid_out.
    pose proof
      (accepting_runs_from_app_ge m q0 w_in r (wmid ++ w_out))
      as Hprefix.
    pose proof
      (ambiguity_of_word_start_ge
         (fnfa_base m) q0 (w_in ++ (wmid ++ w_out)) Hstart)
      as Hamb.
    unfold da_from_to in *.
    set (Rin := runs_between m q0 w_in r) in *.
    set (Rmid := runs_between m r wmid s) in *.
    set (Rout := accepting_runs_from (fnfa_base m) s w_out) in *.
    set (Amid :=
      accepting_runs_from (fnfa_base m) r (wmid ++ w_out)) in *.
    set (Aprefix :=
      accepting_runs_from (fnfa_base m) q0 (w_in ++ (wmid ++ w_out))) in *.
    set (Amb :=
      ambiguity_of_word (fnfa_base m) (w_in ++ (wmid ++ w_out))) in *.
    change (Nat.pow n (S d) <= Amb).
    assert (Hmid_to_out : Nat.pow n (S d) <= Amid).
    {
      eapply Nat.le_trans with (m := Rmid * Rout).
      - nia.
      - exact Hmid_out.
    }
    assert (Hprefix_lower : Nat.pow n (S d) <= Aprefix).
    {
      eapply Nat.le_trans with (m := Rin * Amid).
      - nia.
      - exact Hprefix.
    }
    nia.
  Qed.

  Theorem EDA_exponentially_ambiguous :
    forall (m : @finite_nfa A),
      EDA m ->
      exponentially_ambiguous (fnfa_base m).
  Proof.
    intros m Heda n.
    destruct Heda as [q [v [Huseful [_Hloop Hcount]]]].
    destruct Huseful as [q0 [qf [w_in [w_out
      [Hstart [Hpath_in [Hpath_out Hfinal]]]]]]].
    exists (w_in ++ repeat_word v n ++ w_out).
    set (mid := repeat_word v n).
    pose proof (path_runs_between_positive m q0 w_in q Hpath_in)
      as Hin_pos.
    pose proof
      (path_accepting_runs_from_positive
         (fnfa_base m) q w_out qf Hpath_out Hfinal)
      as Hout_pos.
    pose proof (runs_between_repeat_word_ge_pow m q v n Hcount)
      as Hmid_pow.
    fold mid in Hmid_pow.
    pose proof
      (accepting_runs_from_app_ge m q mid q w_out)
      as Hmid_out.
    pose proof
      (accepting_runs_from_app_ge m q0 w_in q (mid ++ w_out))
      as Hprefix.
    pose proof
      (ambiguity_of_word_start_ge
         (fnfa_base m) q0 (w_in ++ (mid ++ w_out)) Hstart)
      as Hamb.
    set (Rin := runs_between m q0 w_in q) in *.
    set (Rmid := da_from_to m q mid q) in *.
    set (Rout := accepting_runs_from (fnfa_base m) q w_out) in *.
    set (Amid :=
      accepting_runs_from (fnfa_base m) q (mid ++ w_out)) in *.
    set (Aprefix :=
      accepting_runs_from (fnfa_base m) q0 (w_in ++ (mid ++ w_out))) in *.
    set (Amb :=
      ambiguity_of_word (fnfa_base m) (w_in ++ (mid ++ w_out))) in *.
    change (Nat.pow 2 n <= Amb).
    assert (Hmid_lower : Nat.pow 2 n <= Rmid * Rout) by nia.
    assert (Hafter_mid : Rmid * Rout <= Amid) by exact Hmid_out.
    assert (Hafter_prefix : Amid <= Aprefix) by nia.
    nia.
  Qed.

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

  Definition step_successors
      (m : @finite_nfa A)
      (q : finite_state m) : list (finite_state m) :=
    concat
      (map
         (fun a => nfa_step (fnfa_base m) q a)
         (fnfa_alphabet m)).

  Fixpoint reachable_stateb
      (fuel : nat)
      (m : @finite_nfa A)
      (p q : finite_state m) : bool :=
    if fnfa_state_eqb m p q then true
    else
      match fuel with
      | O => false
      | S fuel' =>
          existsb
            (fun r => reachable_stateb fuel' m r q)
            (step_successors m p)
      end.

  Definition connected_stateb
      (fuel : nat)
      (m : @finite_nfa A)
      (p q : finite_state m) : bool :=
    reachable_stateb fuel m p q && reachable_stateb fuel m q p.

  Definition state_mem
      (m : @finite_nfa A)
      (q : finite_state m)
      (qs : list (finite_state m)) : bool :=
    existsb (fnfa_state_eqb m q) qs.

  Definition quotient_component (m : @finite_nfa A) : Type :=
    list (finite_state m).

  Definition scc_component_with_fuel
      (fuel : nat)
      (m : @finite_nfa A)
      (q : finite_state m) : quotient_component m :=
    filter
      (fun r => connected_stateb fuel m q r)
      (fnfa_states m).

  Definition remove_component_states
      (m : @finite_nfa A)
      (removed work : list (finite_state m)) : list (finite_state m) :=
    filter (fun q => negb (state_mem m q removed)) work.

  Fixpoint scc_quotient_loop
      (loop_fuel reach_fuel : nat)
      (m : @finite_nfa A)
      (work : list (finite_state m)) : list (quotient_component m) :=
    match loop_fuel with
    | O => []
    | S loop_fuel' =>
        match work with
        | [] => []
        | q :: work' =>
            let c := scc_component_with_fuel reach_fuel m q in
            c ::
              scc_quotient_loop
                loop_fuel'
                reach_fuel
                m
                (remove_component_states m c work')
        end
    end.

  Definition scc_quotient_with_fuel
      (reach_fuel : nat)
      (m : @finite_nfa A) : list (quotient_component m) :=
    scc_quotient_loop
      (length (fnfa_states m))
      reach_fuel
      m
      (fnfa_states m).

  Definition scc_quotient (m : @finite_nfa A) : list (quotient_component m) :=
    scc_quotient_with_fuel (length (fnfa_states m)) m.

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

  Fixpoint idab_chainb
      (fuel : nat)
      (m : @finite_nfa A)
      (d : nat)
      (r s : finite_state m) : bool :=
    match d with
    | O => false
    | S O => idab_pairb fuel m r s
    | S d' =>
        existsb
          (fun s0 =>
             idab_pairb fuel m r s0
             &&
             existsb
               (fun r' =>
                  existsb
                    (fun u =>
                       pathb m s0 u r' && idab_chainb fuel m d' r' s)
                    (words_upto (fnfa_alphabet m) fuel))
               (fnfa_states m))
          (fnfa_states m)
    end.

  Fixpoint idab_chainb_graph
      (word_fuel graph_fuel : nat)
      (m : @finite_nfa A)
      (d : nat)
      (r s : finite_state m) : bool :=
    match d with
    | O => false
    | S O => idab_pairb word_fuel m r s
    | S d' =>
        existsb
          (fun s0 =>
             idab_pairb word_fuel m r s0
             &&
             existsb
               (fun r' =>
                  reachable_stateb graph_fuel m s0 r'
                  && idab_chainb_graph word_fuel graph_fuel m d' r' s)
               (fnfa_states m))
          (fnfa_states m)
    end.

  Definition g5_red_edgeb
      (word_fuel : nat)
      (m : @finite_nfa A)
      (c d : quotient_component m) : bool :=
    existsb
      (fun p => existsb (fun q => idab_pairb word_fuel m p q) d)
      c.

  Definition g5_plain_edgeb
      (graph_fuel : nat)
      (m : @finite_nfa A)
      (c d : quotient_component m) : bool :=
    existsb
      (fun p => existsb (fun q => reachable_stateb graph_fuel m p q) d)
      c.

  Definition g5_edgeb
      (word_fuel graph_fuel : nat)
      (m : @finite_nfa A)
      (c d : quotient_component m) : bool :=
    g5_red_edgeb word_fuel m c d || g5_plain_edgeb graph_fuel m c d.

  Definition idab_d_with_fuel
      (fuel : nat)
      (m : @finite_nfa A)
      (d : nat) : bool :=
    match d with
    | O => true
    | S _ =>
        existsb
          (fun r =>
             existsb
               (fun s => idab_chainb fuel m d r s)
               (fnfa_states m))
          (fnfa_states m)
    end.

  Definition idab_d_graph_with_fuel
      (word_fuel graph_fuel : nat)
      (m : @finite_nfa A)
      (d : nat) : bool :=
    match d with
    | O => true
    | S _ =>
        existsb
          (fun r =>
             existsb
               (fun s => idab_chainb_graph word_fuel graph_fuel m d r s)
               (fnfa_states m))
          (fnfa_states m)
    end.

  Fixpoint max_ida_depth_with_fuel
      (fuel : nat)
      (m : @finite_nfa A)
      (max_d : nat) : nat :=
    match max_d with
    | O => 0
    | S max_d' =>
        if idab_d_with_fuel fuel m (S max_d')
        then S max_d'
        else max_ida_depth_with_fuel fuel m max_d'
    end.

  Fixpoint max_ida_depth_graph_with_fuel
      (word_fuel graph_fuel : nat)
      (m : @finite_nfa A)
      (max_d : nat) : nat :=
    match max_d with
    | O => 0
    | S max_d' =>
        if idab_d_graph_with_fuel word_fuel graph_fuel m (S max_d')
        then S max_d'
        else max_ida_depth_graph_with_fuel word_fuel graph_fuel m max_d'
    end.

  Fixpoint g5_max_red_path_from
      (path_fuel word_fuel graph_fuel : nat)
      (m : @finite_nfa A)
      (components : list (quotient_component m))
      (c : quotient_component m) : nat :=
    match path_fuel with
    | O => 0
    | S path_fuel' =>
        max_nats
          (map
             (fun d =>
                if g5_edgeb word_fuel graph_fuel m c d
                then
                  (if g5_red_edgeb word_fuel m c d then 1 else 0) +
                  g5_max_red_path_from
                    path_fuel'
                    word_fuel
                    graph_fuel
                    m
                    components
                    d
                else 0)
             components)
    end.

  Definition g5_max_red_path_with_fuel
      (word_fuel graph_fuel : nat)
      (m : @finite_nfa A) : nat :=
    let components := scc_quotient_with_fuel graph_fuel m in
    max_nats
      (map
         (g5_max_red_path_from
            (length components)
            word_fuel
            graph_fuel
            m
            components)
         components).

  Definition g5_has_red_self_loopb
      (word_fuel graph_fuel : nat)
      (m : @finite_nfa A) : bool :=
    let components := scc_quotient_with_fuel graph_fuel m in
    existsb (fun c => g5_red_edgeb word_fuel m c c) components.

  Fixpoint g5_red_pathb_from
      (path_fuel word_fuel graph_fuel : nat)
      (m : @finite_nfa A)
      (components : list (quotient_component m))
      (red_count : nat)
      (c : quotient_component m) : bool :=
    match red_count with
    | O => true
    | S red_count' =>
        match path_fuel with
        | O => false
        | S path_fuel' =>
            existsb
              (fun d =>
                 if g5_edgeb word_fuel graph_fuel m c d
                 then
                   if g5_red_edgeb word_fuel m c d
                   then
                     g5_red_pathb_from
                       path_fuel'
                       word_fuel
                       graph_fuel
                       m
                       components
                       red_count'
                       d
                   else
                     g5_red_pathb_from
                       path_fuel'
                       word_fuel
                       graph_fuel
                       m
                       components
                       (S red_count')
                       d
                 else false)
              components
        end
    end.

  Definition g5_red_pathb_with_fuel
      (word_fuel graph_fuel : nat)
      (m : @finite_nfa A)
      (red_count : nat) : bool :=
    let components := scc_quotient_with_fuel graph_fuel m in
    match red_count with
    | O => true
    | S _ =>
        existsb
          (g5_red_pathb_from
             (length components)
             word_fuel
             graph_fuel
             m
             components
             red_count)
          components
    end.

  Fixpoint max_g5_red_depth_with_fuel
      (word_fuel graph_fuel : nat)
      (m : @finite_nfa A)
      (max_d : nat) : nat :=
    match max_d with
    | O => 0
    | S max_d' =>
        if g5_red_pathb_with_fuel word_fuel graph_fuel m (S max_d')
        then S max_d'
        else max_g5_red_depth_with_fuel word_fuel graph_fuel m max_d'
    end.

  Lemma max_g5_red_depth_with_fuel_le :
    forall word_fuel graph_fuel (m : @finite_nfa A) max_d,
      max_g5_red_depth_with_fuel word_fuel graph_fuel m max_d <= max_d.
  Proof.
    intros word_fuel graph_fuel m max_d.
    induction max_d as [| max_d IH]; simpl.
    - lia.
    - change
        ((if g5_red_pathb_with_fuel word_fuel graph_fuel m (S max_d)
          then S max_d
          else max_g5_red_depth_with_fuel word_fuel graph_fuel m max_d)
          <= S max_d).
      destruct (g5_red_pathb_with_fuel word_fuel graph_fuel m (S max_d)).
      + apply Nat.le_refl.
      + eapply Nat.le_trans.
        * exact IH.
        * lia.
  Qed.

  Fixpoint g5_walkb_from
      (word_fuel graph_fuel : nat)
      (m : @finite_nfa A)
      (c : quotient_component m)
      (walk : list (quotient_component m)) : bool :=
    match walk with
    | [] => true
    | d :: walk' =>
        g5_edgeb word_fuel graph_fuel m c d
        && g5_walkb_from word_fuel graph_fuel m d walk'
    end.

  Definition g5_walkb
      (word_fuel graph_fuel : nat)
      (m : @finite_nfa A)
      (walk : list (quotient_component m)) : bool :=
    match walk with
    | [] => true
    | c :: walk' => g5_walkb_from word_fuel graph_fuel m c walk'
    end.

  Fixpoint g5_red_edges_on_walk_from
      (word_fuel : nat)
      (m : @finite_nfa A)
      (c : quotient_component m)
      (walk : list (quotient_component m)) : nat :=
    match walk with
    | [] => 0
    | d :: walk' =>
        (if g5_red_edgeb word_fuel m c d then 1 else 0) +
        g5_red_edges_on_walk_from word_fuel m d walk'
    end.

  Definition g5_red_edges_on_walk
      (word_fuel : nat)
      (m : @finite_nfa A)
      (walk : list (quotient_component m)) : nat :=
    match walk with
    | [] => 0
    | c :: walk' => g5_red_edges_on_walk_from word_fuel m c walk'
    end.

  Lemma g5_red_edges_on_walk_from_le_length :
    forall word_fuel (m : @finite_nfa A) c walk,
      g5_red_edges_on_walk_from word_fuel m c walk <= length walk.
  Proof.
    intros word_fuel m c walk.
    revert c.
    induction walk as [| d walk IH]; intros c; simpl.
    - lia.
    - destruct (g5_red_edgeb word_fuel m c d); simpl; specialize (IH d); lia.
  Qed.

  Lemma g5_red_edges_on_walk_le_pred_length :
    forall word_fuel (m : @finite_nfa A) walk,
      g5_red_edges_on_walk word_fuel m walk <= length walk.
  Proof.
    intros word_fuel m walk.
    destruct walk as [| c walk']; simpl.
    - lia.
    - pose proof (g5_red_edges_on_walk_from_le_length word_fuel m c walk').
      lia.
  Qed.

  Lemma g5_red_edges_on_walk_le_edges :
    forall word_fuel (m : @finite_nfa A) walk,
      g5_red_edges_on_walk word_fuel m walk <= pred (length walk).
  Proof.
    intros word_fuel m walk.
    destruct walk as [| c walk']; simpl.
    - lia.
    - apply g5_red_edges_on_walk_from_le_length.
  Qed.

  Fixpoint g5_red_positions_from
      (idx word_fuel : nat)
      (m : @finite_nfa A)
      (c : quotient_component m)
      (walk : list (quotient_component m)) : list nat :=
    match walk with
    | [] => []
    | d :: walk' =>
        let rest := g5_red_positions_from (S idx) word_fuel m d walk' in
        if g5_red_edgeb word_fuel m c d then idx :: rest else rest
    end.

  Definition g5_red_positions_on_walk
      (word_fuel : nat)
      (m : @finite_nfa A)
      (walk : list (quotient_component m)) : list nat :=
    match walk with
    | [] => []
    | c :: walk' => g5_red_positions_from 0 word_fuel m c walk'
    end.

  Lemma g5_red_positions_from_length :
    forall idx word_fuel (m : @finite_nfa A) c walk,
      length (g5_red_positions_from idx word_fuel m c walk) =
        g5_red_edges_on_walk_from word_fuel m c walk.
  Proof.
    intros idx word_fuel m c walk.
    revert idx c.
    induction walk as [| d walk IH]; intros idx c; simpl.
    - reflexivity.
    - destruct (g5_red_edgeb word_fuel m c d); simpl;
        now rewrite IH.
  Qed.

  Lemma g5_red_positions_on_walk_length :
    forall word_fuel (m : @finite_nfa A) walk,
      length (g5_red_positions_on_walk word_fuel m walk) =
        g5_red_edges_on_walk word_fuel m walk.
  Proof.
    intros word_fuel m walk.
    destruct walk as [| c walk']; simpl.
    - reflexivity.
    - apply g5_red_positions_from_length.
  Qed.

  Lemma g5_red_positions_from_nth_bound :
    forall idx word_fuel (m : @finite_nfa A) c walk i pos,
      nth_error
        (g5_red_positions_from idx word_fuel m c walk)
        i = Some pos ->
      idx <= pos /\ pos < idx + length walk.
  Proof.
    intros idx word_fuel m c walk.
    revert idx c.
    induction walk as [| d walk IH]; intros idx c i pos Hnth; simpl in Hnth.
    - destruct i; simpl in Hnth; discriminate.
    - destruct (g5_red_edgeb word_fuel m c d) eqn:Hred.
      + destruct i as [| i]; simpl in Hnth.
        * injection Hnth as Hpos.
          subst pos.
          simpl. split; lia.
        * specialize (IH (S idx) d i pos Hnth) as [Hlo Hhi].
          simpl. split; lia.
      + specialize (IH (S idx) d i pos Hnth) as [Hlo Hhi].
        simpl. split; lia.
  Qed.

  Lemma g5_red_positions_on_walk_nth_bound :
    forall word_fuel (m : @finite_nfa A) walk i pos,
      nth_error (g5_red_positions_on_walk word_fuel m walk) i = Some pos ->
      pos < length walk.
  Proof.
    intros word_fuel m walk i pos Hnth.
    destruct walk as [| c walk']; simpl in Hnth.
    - destruct i; simpl in Hnth; discriminate.
    - destruct
        (g5_red_positions_from_nth_bound
          0 word_fuel m c walk' i pos Hnth)
        as [_ Hhi].
      simpl. lia.
  Qed.

  Lemma g5_red_positions_on_walk_In_bound :
    forall word_fuel (m : @finite_nfa A) walk pos,
      In pos (g5_red_positions_on_walk word_fuel m walk) ->
      pos < length walk.
  Proof.
    intros word_fuel m walk pos Hin.
    apply In_nth_error in Hin as [i Hnth].
    eapply g5_red_positions_on_walk_nth_bound; eauto.
  Qed.

  Definition g5_red_position_vector
      (d word_fuel : nat)
      (m : @finite_nfa A)
      (walk : list (quotient_component m)) : list nat :=
    pad_nat_vector d (g5_red_positions_on_walk word_fuel m walk).

  Lemma g5_red_position_vector_in_nat_vectors :
    forall d bound word_fuel (m : @finite_nfa A) walk,
      g5_red_edges_on_walk word_fuel m walk <= d ->
      length walk <= bound ->
      0 < bound ->
      In
        (g5_red_position_vector d word_fuel m walk)
        (nat_vectors_below d bound).
  Proof.
    intros d bound word_fuel m walk Hred Hlen Hbound.
    unfold g5_red_position_vector.
    apply pad_nat_vector_in_nat_vectors_below.
    - rewrite g5_red_positions_on_walk_length. exact Hred.
    - exact Hbound.
    - intros pos Hpos.
      pose proof
        (g5_red_positions_on_walk_In_bound word_fuel m walk pos Hpos)
        as Hpos_bound.
      lia.
  Qed.

  Inductive ambiguity_growth_result : Type :=
  | GrowthExponential
  | GrowthPolynomialLowerBound (d : nat).

  Definition ambiguity_growth_lower_bound_with_fuel
      (fuel : nat)
      (m : @finite_nfa A)
      (max_d : nat) : ambiguity_growth_result :=
    if edab_with_fuel fuel m
    then GrowthExponential
    else GrowthPolynomialLowerBound
      (max_ida_depth_with_fuel fuel m max_d).

  Definition ambiguity_growth_lower_bound_graph_with_fuel
      (word_fuel graph_fuel : nat)
      (m : @finite_nfa A)
      (max_d : nat) : ambiguity_growth_result :=
    if edab_with_fuel word_fuel m
    then GrowthExponential
    else GrowthPolynomialLowerBound
      (max_ida_depth_graph_with_fuel word_fuel graph_fuel m max_d).

  Definition ambiguity_growth_g5_candidate_with_fuel
      (word_fuel graph_fuel : nat)
      (m : @finite_nfa A) : ambiguity_growth_result :=
    if edab_with_fuel word_fuel m || g5_has_red_self_loopb word_fuel graph_fuel m
    then GrowthExponential
    else GrowthPolynomialLowerBound
      (g5_max_red_path_with_fuel word_fuel graph_fuel m).

  Definition ambiguity_growth_g5_lower_bound_with_fuel
      (word_fuel graph_fuel : nat)
      (m : @finite_nfa A) : ambiguity_growth_result :=
    let components := scc_quotient_with_fuel graph_fuel m in
    if edab_with_fuel word_fuel m || g5_has_red_self_loopb word_fuel graph_fuel m
    then GrowthExponential
    else GrowthPolynomialLowerBound
      (max_g5_red_depth_with_fuel
         word_fuel
         graph_fuel
         m
         (length components)).

  Definition polynomial_growth_upper_bound (m : @nfa A) (d : nat) : Prop :=
    exists c,
      forall w,
        ambiguity_of_word m w <= c * Nat.pow (S (length w)) d.

  Definition degree_at_most := polynomial_growth_upper_bound.

  Definition polynomial_growth_upper_bound_on_alphabet
      (m : @finite_nfa A)
      (d : nat) : Prop :=
    exists c,
      forall w,
        word_in_alphabet m w ->
        ambiguity_of_word (fnfa_base m) w <=
          c * Nat.pow (S (length w)) d.

  Definition degree_at_most_on_alphabet :=
    polynomial_growth_upper_bound_on_alphabet.

  Definition alphabet_complete (m : @finite_nfa A) : Prop :=
    forall a, In a (fnfa_alphabet m).

  Definition exact_polynomial_degree (m : @nfa A) (d : nat) : Prop :=
    degree_at_least m d /\ degree_at_most m d.

  Definition exact_polynomial_degree_on_alphabet
      (m : @finite_nfa A)
      (d : nat) : Prop :=
    degree_at_least (fnfa_base m) d /\ degree_at_most_on_alphabet m d.

  Definition no_EDA (m : @finite_nfa A) : Prop := ~ EDA m.

  Definition fnfa_start_nodup (m : @finite_nfa A) : Prop :=
    NoDup (nfa_start (fnfa_base m)).

  Definition fnfa_step_nodup (m : @finite_nfa A) : Prop :=
    forall q a, NoDup (nfa_step (fnfa_base m) q a).

  Definition fnfa_choice_nodup (m : @finite_nfa A) : Prop :=
    fnfa_start_nodup m /\ fnfa_step_nodup m.

  Lemma EDA_from_two_distinct_loop_choices :
    forall (m : @finite_nfa A) q v c1 c2,
      finite_useful m q ->
      In c1 (run_choices_between m q v q) ->
      In c2 (run_choices_between m q v q) ->
      c1 <> c2 ->
      EDA m.
  Proof.
    intros m q v c1 c2 Huseful Hc1 Hc2 Hneq.
    exists q, v.
    repeat split.
    - exact Huseful.
    - apply run_choices_from_path with (choices := c1).
      now apply run_choices_between_In_choices.
    - now apply two_distinct_run_choices_between_ge_two
        with (c1 := c1) (c2 := c2).
  Qed.

  Lemma EDA_from_two_distinct_choices_with_return :
    forall (m : @finite_nfa A) q v r u c1 c2,
      finite_useful m q ->
      In c1 (run_choices_between m q v r) ->
      In c2 (run_choices_between m q v r) ->
      c1 <> c2 ->
      finite_delta_star m r u q ->
      EDA m.
  Proof.
    intros m q v r u c1 c2 Huseful Hc1 Hc2 Hneq Hreturn.
    destruct
      (run_choices_between_exists_from_path m r u q Hreturn)
      as [cret Hcret].
    assert (Hloop1 : In (c1 ++ cret) (run_choices_between m q (v ++ u) q)).
    {
      apply run_choices_between_complete.
      apply run_choices_from_app with (mid := r).
      - now apply run_choices_between_In_choices.
      - now apply run_choices_between_In_choices.
    }
    assert (Hloop2 : In (c2 ++ cret) (run_choices_between m q (v ++ u) q)).
    {
      apply run_choices_between_complete.
      apply run_choices_from_app with (mid := r).
      - now apply run_choices_between_In_choices.
      - now apply run_choices_between_In_choices.
    }
    eapply EDA_from_two_distinct_loop_choices
      with (q := q) (v := v ++ u)
        (c1 := c1 ++ cret) (c2 := c2 ++ cret).
    - exact Huseful.
    - exact Hloop1.
    - exact Hloop2.
    - intros Happ.
      apply Hneq.
      now apply app_inv_tail in Happ.
  Qed.

  Lemma no_EDA_same_component_choices_unique :
    forall (m : @finite_nfa A) q v r u c1 c2,
      no_EDA m ->
      finite_useful m q ->
      In c1 (run_choices_between m q v r) ->
      In c2 (run_choices_between m q v r) ->
      finite_delta_star m r u q ->
      c1 = c2.
  Proof.
    intros m q v r u c1 c2 Hno Huseful Hc1 Hc2 Hreturn.
    destruct (list_eq_dec Nat.eq_dec c1 c2) as [Heq | Hneq];
      [exact Heq |].
    exfalso. apply Hno.
    eapply EDA_from_two_distinct_choices_with_return
      with (q := q) (v := v) (r := r) (u := u)
        (c1 := c1) (c2 := c2); eauto.
  Qed.

  Lemma degree_at_most_on_alphabet_from_global :
    forall (m : @finite_nfa A) d,
      degree_at_most (fnfa_base m) d ->
      degree_at_most_on_alphabet m d.
  Proof.
    intros m d [c Hbound].
    exists c.
    intros w _Hall.
    apply Hbound.
  Qed.

  Lemma word_in_alphabet_complete :
    forall (m : @finite_nfa A) w,
      alphabet_complete m ->
      word_in_alphabet m w.
  Proof.
    intros m w Hcomplete.
    induction w as [| a w IH]; constructor; auto.
  Qed.

  Lemma degree_at_most_from_on_alphabet_complete :
    forall (m : @finite_nfa A) d,
      alphabet_complete m ->
      degree_at_most_on_alphabet m d ->
      degree_at_most (fnfa_base m) d.
  Proof.
    intros m d Hcomplete [c Hbound].
    exists c.
    intros w.
    apply Hbound.
    now apply word_in_alphabet_complete.
  Qed.

  Lemma degree_at_most_step :
    forall (m : @nfa A) d,
      degree_at_most m d ->
      degree_at_most m (S d).
  Proof.
    intros m d [c Hbound].
    exists c.
    intros w.
    specialize (Hbound w).
    simpl.
    nia.
  Qed.

  Lemma degree_at_most_mono :
    forall (m : @nfa A) d e,
      d <= e ->
      degree_at_most m d ->
      degree_at_most m e.
  Proof.
    intros m d e Hle Hupper.
    induction Hle.
    - exact Hupper.
    - now apply degree_at_most_step.
  Qed.

  Lemma degree_at_most_on_alphabet_step :
    forall (m : @finite_nfa A) d,
      degree_at_most_on_alphabet m d ->
      degree_at_most_on_alphabet m (S d).
  Proof.
    intros m d [c Hbound].
    exists c.
    intros w Hall.
    specialize (Hbound w Hall).
    simpl.
    nia.
  Qed.

  Lemma degree_at_most_on_alphabet_mono :
    forall (m : @finite_nfa A) d e,
      d <= e ->
      degree_at_most_on_alphabet m d ->
      degree_at_most_on_alphabet m e.
  Proof.
    intros m d e Hle Hupper.
    induction Hle.
    - exact Hupper.
    - now apply degree_at_most_on_alphabet_step.
  Qed.

  Definition accepting_runs_from_upper_on_alphabet
      (m : @finite_nfa A)
      (q : finite_state m)
      (d c : nat) : Prop :=
    forall w,
      word_in_alphabet m w ->
      accepting_runs_from (fnfa_base m) q w <=
        c * Nat.pow (S (length w)) d.

  Definition accepting_endpoints_upper_on_alphabet
      (m : @finite_nfa A)
      (d c : nat) : Prop :=
    forall w,
      word_in_alphabet m w ->
      length (accepting_run_endpoints m w) <=
        c * Nat.pow (S (length w)) d.

  Definition accepting_endpoint_occurrence_codes_upper_on_alphabet
      (m : @finite_nfa A)
      (Code : Type)
      (d c : nat) : Prop :=
    forall w,
      word_in_alphabet m w ->
      exists codes : list Code,
        NoDup codes /\
        length codes <= c * Nat.pow (S (length w)) d /\
        exists encode : nat -> Code,
          (forall i,
            i < length (accepting_run_endpoints m w) ->
            In (encode i) codes) /\
          (forall i j,
            i < length (accepting_run_endpoints m w) ->
            j < length (accepting_run_endpoints m w) ->
            encode i = encode j ->
            i = j).

  Lemma accepting_endpoints_upper_on_alphabet_from_occurrence_codes :
    forall (m : @finite_nfa A) (Code : Type) d c,
      accepting_endpoint_occurrence_codes_upper_on_alphabet m Code d c ->
      accepting_endpoints_upper_on_alphabet m d c.
  Proof.
    intros m Code d c Hcodes w Hall.
    destruct (Hcodes w Hall) as
      [codes [Hnodup [Hlen [encode [Hinto Hinj]]]]].
    eapply Nat.le_trans.
    - eapply length_le_from_index_injection; eauto.
    - exact Hlen.
  Qed.

  Lemma degree_at_most_on_alphabet_from_accepting_endpoints_bound :
    forall (m : @finite_nfa A) d c,
      accepting_endpoints_upper_on_alphabet m d c ->
      degree_at_most_on_alphabet m d.
  Proof.
    intros m d c Hbound.
    exists c.
    intros w Hall.
    rewrite <- accepting_run_endpoints_length.
    now apply Hbound.
  Qed.

  Lemma degree_at_most_on_alphabet_from_occurrence_codes :
    forall (m : @finite_nfa A) (Code : Type) d c,
      accepting_endpoint_occurrence_codes_upper_on_alphabet m Code d c ->
      degree_at_most_on_alphabet m d.
  Proof.
    intros m Code d c Hcodes.
    apply degree_at_most_on_alphabet_from_accepting_endpoints_bound
      with (c := c).
    now apply accepting_endpoints_upper_on_alphabet_from_occurrence_codes
      with (Code := Code).
  Qed.

  Definition accepting_endpoint_polynomial_signatures_on_alphabet
      (m : @finite_nfa A)
      (Payload : Type)
      (payloads : list Payload)
      (d c : nat) : Prop :=
    NoDup payloads /\
    length payloads <= c /\
    forall w,
      word_in_alphabet m w ->
      exists encode : nat -> list nat * Payload,
        (forall i,
          i < length (accepting_run_endpoints m w) ->
          In (encode i)
            (polynomial_signature_codes payloads d (S (length w)))) /\
        (forall i j,
          i < length (accepting_run_endpoints m w) ->
          j < length (accepting_run_endpoints m w) ->
          encode i = encode j ->
          i = j).

  Lemma accepting_endpoint_occurrence_codes_upper_on_alphabet_from_polynomial_signatures :
    forall (m : @finite_nfa A) (Payload : Type) payloads d c,
      accepting_endpoint_polynomial_signatures_on_alphabet
        m Payload payloads d c ->
      accepting_endpoint_occurrence_codes_upper_on_alphabet
        m (list nat * Payload) d c.
  Proof.
    intros m Payload payloads d c [Hnodup [Hpayload Hsignatures]] w Hall.
    destruct (Hsignatures w Hall) as [encode [Hinto Hinj]].
    exists (polynomial_signature_codes payloads d (S (length w))).
    split.
    - now apply polynomial_signature_codes_NoDup.
    - split.
      + rewrite polynomial_signature_codes_length.
        nia.
      + exists encode.
        split; assumption.
  Qed.

  Lemma degree_at_most_on_alphabet_from_polynomial_signatures :
    forall (m : @finite_nfa A) (Payload : Type) payloads d c,
      accepting_endpoint_polynomial_signatures_on_alphabet
        m Payload payloads d c ->
      degree_at_most_on_alphabet m d.
  Proof.
    intros m Payload payloads d c Hsignatures.
    eapply degree_at_most_on_alphabet_from_occurrence_codes.
    eapply accepting_endpoint_occurrence_codes_upper_on_alphabet_from_polynomial_signatures.
    exact Hsignatures.
  Qed.

  Definition accepting_endpoint_g5_walk_signatures_on_alphabet
      (word_fuel : nat)
      (m : @finite_nfa A)
      (Payload : Type)
      (payloads : list Payload)
      (d c : nat) : Prop :=
    NoDup payloads /\
    length payloads <= c /\
    forall w,
      word_in_alphabet m w ->
      exists walk_of : nat -> list (quotient_component m),
      exists payload_of : nat -> Payload,
        (forall i,
          i < length (accepting_run_endpoints m w) ->
          In (payload_of i) payloads /\
          g5_red_edges_on_walk word_fuel m (walk_of i) <= d /\
          length (walk_of i) <= S (length w)) /\
        (forall i j,
          i < length (accepting_run_endpoints m w) ->
          j < length (accepting_run_endpoints m w) ->
          (g5_red_position_vector d word_fuel m (walk_of i),
            payload_of i) =
          (g5_red_position_vector d word_fuel m (walk_of j),
            payload_of j) ->
          i = j).

  Lemma accepting_endpoint_polynomial_signatures_from_g5_walk_signatures :
    forall word_fuel (m : @finite_nfa A) (Payload : Type) payloads d c,
      accepting_endpoint_g5_walk_signatures_on_alphabet
        word_fuel m Payload payloads d c ->
      accepting_endpoint_polynomial_signatures_on_alphabet
        m Payload payloads d c.
  Proof.
    intros word_fuel m Payload payloads d c
      [Hnodup [Hpayload Hwalk_signatures]].
    repeat split; auto.
    intros w Hall.
    destruct (Hwalk_signatures w Hall) as
      [walk_of [payload_of [Hvalid Hinj]]].
    exists
      (fun i =>
        (g5_red_position_vector d word_fuel m (walk_of i),
         payload_of i)).
    split.
    - intros i Hi.
      destruct (Hvalid i Hi) as [Hpayload_i [Hred Hlen_walk]].
      apply polynomial_signature_codes_In.
      + apply g5_red_position_vector_in_nat_vectors.
        * exact Hred.
        * exact Hlen_walk.
        * lia.
      + exact Hpayload_i.
    - exact Hinj.
  Qed.

  Lemma degree_at_most_on_alphabet_from_g5_walk_signatures :
    forall word_fuel (m : @finite_nfa A) (Payload : Type) payloads d c,
      accepting_endpoint_g5_walk_signatures_on_alphabet
        word_fuel m Payload payloads d c ->
      degree_at_most_on_alphabet m d.
  Proof.
    intros word_fuel m Payload payloads d c Hwalk_signatures.
    eapply degree_at_most_on_alphabet_from_polynomial_signatures.
    eapply accepting_endpoint_polynomial_signatures_from_g5_walk_signatures.
    exact Hwalk_signatures.
  Qed.

  Definition accepting_run_polynomial_signatures_on_alphabet
      (m : @finite_nfa A)
      (Payload : Type)
      (payloads : list Payload)
      (d c : nat) : Prop :=
    NoDup payloads /\
    length payloads <= c /\
    forall w,
      word_in_alphabet m w ->
      exists encode : nat -> list nat * Payload,
        (forall i,
          i < length (accepting_run_full_choices m w) ->
          In (encode i)
            (polynomial_signature_codes payloads d (S (length w)))) /\
        (forall i j,
          i < length (accepting_run_full_choices m w) ->
          j < length (accepting_run_full_choices m w) ->
          encode i = encode j ->
          i = j).

  Lemma degree_at_most_on_alphabet_from_run_polynomial_signatures :
    forall (m : @finite_nfa A) (Payload : Type) payloads d c,
      accepting_run_polynomial_signatures_on_alphabet
        m Payload payloads d c ->
      degree_at_most_on_alphabet m d.
  Proof.
    intros m Payload payloads d c [Hnodup [Hpayload Hsignatures]].
    exists c.
    intros w Hall.
    rewrite <- accepting_run_full_choices_length.
    destruct (Hsignatures w Hall) as [encode [Hinto Hinj]].
    eapply Nat.le_trans.
    - eapply length_le_from_index_injection.
      + apply (@polynomial_signature_codes_NoDup Payload).
        exact Hnodup.
      + intros i Hi. apply Hinto. exact Hi.
      + intros i j Hi Hj Heq. eapply Hinj; eauto.
    - rewrite polynomial_signature_codes_length.
      nia.
  Qed.

  Definition accepting_run_g5_walk_signatures_on_alphabet
      (word_fuel : nat)
      (m : @finite_nfa A)
      (Payload : Type)
      (payloads : list Payload)
      (d c : nat) : Prop :=
    NoDup payloads /\
    length payloads <= c /\
    forall w,
      word_in_alphabet m w ->
      exists walk_of : nat -> list (quotient_component m),
      exists payload_of : nat -> Payload,
        (forall i,
          i < length (accepting_run_full_choices m w) ->
          In (payload_of i) payloads /\
          g5_red_edges_on_walk word_fuel m (walk_of i) <= d /\
          length (walk_of i) <= S (length w)) /\
        (forall i j,
          i < length (accepting_run_full_choices m w) ->
          j < length (accepting_run_full_choices m w) ->
          (g5_red_position_vector d word_fuel m (walk_of i),
            payload_of i) =
          (g5_red_position_vector d word_fuel m (walk_of j),
            payload_of j) ->
          i = j).

  Lemma accepting_run_polynomial_signatures_from_g5_walk_signatures :
    forall word_fuel (m : @finite_nfa A) (Payload : Type) payloads d c,
      accepting_run_g5_walk_signatures_on_alphabet
        word_fuel m Payload payloads d c ->
      accepting_run_polynomial_signatures_on_alphabet
        m Payload payloads d c.
  Proof.
    intros word_fuel m Payload payloads d c
      [Hnodup [Hpayload Hwalk_signatures]].
    repeat split; auto.
    intros w Hall.
    destruct (Hwalk_signatures w Hall) as
      [walk_of [payload_of [Hvalid Hinj]]].
    exists
      (fun i =>
        (g5_red_position_vector d word_fuel m (walk_of i),
         payload_of i)).
    split.
    - intros i Hi.
      destruct (Hvalid i Hi) as [Hpayload_i [Hred Hlen_walk]].
      apply polynomial_signature_codes_In.
      + apply g5_red_position_vector_in_nat_vectors.
        * exact Hred.
        * exact Hlen_walk.
        * lia.
      + exact Hpayload_i.
    - exact Hinj.
  Qed.

  Lemma degree_at_most_on_alphabet_from_run_g5_walk_signatures :
    forall word_fuel (m : @finite_nfa A) (Payload : Type) payloads d c,
      accepting_run_g5_walk_signatures_on_alphabet
        word_fuel m Payload payloads d c ->
      degree_at_most_on_alphabet m d.
  Proof.
    intros word_fuel m Payload payloads d c Hwalk_signatures.
    eapply degree_at_most_on_alphabet_from_run_polynomial_signatures.
    eapply accepting_run_polynomial_signatures_from_g5_walk_signatures.
    exact Hwalk_signatures.
  Qed.

  Lemma degree_at_most_on_alphabet_from_start_state_bounds :
    forall (m : @finite_nfa A) d c,
      (forall q,
        In q (nfa_start (fnfa_base m)) ->
        accepting_runs_from_upper_on_alphabet m q d c) ->
      degree_at_most_on_alphabet m d.
  Proof.
    intros m d c Hbounds.
    exists (length (nfa_start (fnfa_base m)) * c).
    intros w Hall.
    unfold ambiguity_of_word.
    eapply Nat.le_trans.
    - apply sum_nats_map_le_const.
      intros q Hq.
      apply Hbounds; assumption.
    - nia.
  Qed.

  Lemma degree_at_most_on_alphabet_from_state_bounds :
    forall (m : @finite_nfa A) d c,
      fnfa_well_formed m ->
      (forall q,
        In q (fnfa_states m) ->
        accepting_runs_from_upper_on_alphabet m q d c) ->
      degree_at_most_on_alphabet m d.
  Proof.
    intros m d c Hwf Hbounds.
    apply degree_at_most_on_alphabet_from_start_state_bounds with (c := c).
    intros q Hstart w Hall.
    apply Hbounds.
    - destruct Hwf as [Hstarts _].
      now apply Hstarts.
    - exact Hall.
  Qed.

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

  Lemma step_successors_In :
    forall (m : @finite_nfa A) p q,
      In q (step_successors m p) ->
      exists a,
        In a (fnfa_alphabet m) /\
        In q (nfa_step (fnfa_base m) p a).
  Proof.
    intros m p q H.
    unfold step_successors in H.
    apply in_concat in H as [qs [Hqs Hq]].
    apply in_map_iff in Hqs as [a [Heq Ha]].
    subst qs.
    exists a. split; assumption.
  Qed.

  Lemma step_successors_edge_In :
    forall (m : @finite_nfa A) p q a,
      In a (fnfa_alphabet m) ->
      In q (nfa_step (fnfa_base m) p a) ->
      In q (step_successors m p).
  Proof.
    intros m p q a Ha Hq.
    unfold step_successors.
    apply in_concat.
    exists (nfa_step (fnfa_base m) p a).
    split; auto.
    apply in_map_iff.
    exists a. split; auto.
  Qed.

  Lemma reachable_stateb_sound :
    forall fuel (m : @finite_nfa A) p q,
      reachable_stateb fuel m p q = true ->
      exists w, finite_delta_star m p w q.
  Proof.
    induction fuel as [| fuel IH]; intros m p q H.
    - simpl in H.
      destruct (fnfa_state_eqb m p q) eqn:Heq; try discriminate.
      apply fnfa_state_eqb_sound in Heq. subst.
      exists []. constructor.
    - simpl in H.
      destruct (fnfa_state_eqb m p q) eqn:Heq.
      + apply fnfa_state_eqb_sound in Heq. subst.
        exists []. constructor.
      + apply existsb_exists in H as [r [Hr Hreach]].
        destruct (step_successors_In m p r Hr) as [a [_Ha Hstep]].
        destruct (IH m r q Hreach) as [w Hpath].
        exists (a :: w).
        eapply Path_cons; eauto.
  Qed.

  Lemma reachable_stateb_complete_path :
    forall fuel (m : @finite_nfa A) p w q,
      length w <= fuel ->
      Forall (fun a => In a (fnfa_alphabet m)) w ->
      finite_delta_star m p w q ->
      reachable_stateb fuel m p q = true.
  Proof.
    induction fuel as [| fuel IH]; intros m p w q Hlen Hall Hpath.
    - destruct w as [| a w]; simpl in Hlen; try lia.
      inversion Hpath; subst.
      simpl.
      rewrite (fnfa_state_eqb_complete m q q eq_refl).
      reflexivity.
    - simpl.
      destruct (fnfa_state_eqb m p q) eqn:Heq; auto.
      destruct w as [| a w].
      + inversion Hpath; subst.
        rewrite (fnfa_state_eqb_complete m q q eq_refl) in Heq.
        discriminate.
      + inversion Hpath as [| p0 a0 q' w' q'' Hstep Htail]; subst.
        inversion Hall as [| a1 w1 Ha Hall_tail]; subst.
        apply existsb_exists.
        exists q'. split.
        * eapply step_successors_edge_In; eauto.
        * eapply IH; eauto.
          simpl in Hlen. lia.
  Qed.

  Lemma connected_stateb_sound :
    forall fuel (m : @finite_nfa A) p q,
      connected_stateb fuel m p q = true ->
      connected (fnfa_base m) p q.
  Proof.
    intros fuel m p q H.
    unfold connected_stateb in H.
    apply andb_true_iff in H as [Hpq Hqp].
    destruct (reachable_stateb_sound fuel m p q Hpq) as [u Hu].
    destruct (reachable_stateb_sound fuel m q p Hqp) as [v Hv].
    exists u, v. split; assumption.
  Qed.

  Lemma connected_refl :
    forall (m : @nfa A) q,
      connected m q q.
  Proof.
    intros m q.
    exists [], []. split; constructor.
  Qed.

  Lemma connected_sym :
    forall (m : @nfa A) p q,
      connected m p q ->
      connected m q p.
  Proof.
    intros m p q [u [v [Hpq Hqp]]].
    exists v, u. split; assumption.
  Qed.

  Lemma connected_trans :
    forall (m : @nfa A) p q r,
      connected m p q ->
      connected m q r ->
      connected m p r.
  Proof.
    intros m p q r [u1 [v1 [Hpq Hqp]]] [u2 [v2 [Hqr Hrq]]].
    exists (u1 ++ u2), (v2 ++ v1). split.
    - eapply path_from_app; eauto.
    - eapply path_from_app; eauto.
  Qed.

  Lemma state_mem_sound :
    forall (m : @finite_nfa A) q qs,
      state_mem m q qs = true ->
      In q qs.
  Proof.
    intros m q qs H.
    unfold state_mem in H.
    apply existsb_exists in H as [r [Hr Heq]].
    apply fnfa_state_eqb_sound in Heq.
    now subst r.
  Qed.

  Lemma state_mem_complete :
    forall (m : @finite_nfa A) q qs,
      In q qs ->
      state_mem m q qs = true.
  Proof.
    intros m q qs H.
    unfold state_mem.
    apply existsb_exists.
    exists q. split; auto.
    now apply fnfa_state_eqb_complete.
  Qed.

  Lemma connected_stateb_refl :
    forall fuel (m : @finite_nfa A) q,
      connected_stateb fuel m q q = true.
  Proof.
    intros fuel m q.
    unfold connected_stateb.
    assert (Hreach : reachable_stateb fuel m q q = true).
    {
      destruct fuel; simpl;
        rewrite (fnfa_state_eqb_complete m q q eq_refl);
        reflexivity.
    }
    rewrite Hreach. reflexivity.
  Qed.

  Lemma scc_component_with_fuel_sound :
    forall fuel (m : @finite_nfa A) rep q,
      In q (scc_component_with_fuel fuel m rep) ->
      connected (fnfa_base m) rep q.
  Proof.
    intros fuel m rep q H.
    unfold scc_component_with_fuel in H.
    apply filter_In in H as [_ Hconnected].
    now apply connected_stateb_sound with (fuel := fuel).
  Qed.

  Definition component_connected
      (m : @finite_nfa A)
      (c : quotient_component m) : Prop :=
    forall p q,
      In p c ->
      In q c ->
      connected (fnfa_base m) p q.

  Definition components_connected
      (m : @finite_nfa A)
      (components : list (quotient_component m)) : Prop :=
    forall c,
      In c components ->
      component_connected m c.

  Lemma scc_component_with_fuel_connected :
    forall fuel (m : @finite_nfa A) rep,
      component_connected m (scc_component_with_fuel fuel m rep).
  Proof.
    unfold component_connected.
    intros fuel m rep p q Hp Hq.
    pose proof (scc_component_with_fuel_sound fuel m rep p Hp) as Hrep_p.
    pose proof (scc_component_with_fuel_sound fuel m rep q Hq) as Hrep_q.
    eapply connected_trans with (q := rep).
    - apply connected_sym. exact Hrep_p.
    - exact Hrep_q.
  Qed.

  Lemma scc_component_with_fuel_contains_rep :
    forall fuel (m : @finite_nfa A) rep,
      In rep (fnfa_states m) ->
      In rep (scc_component_with_fuel fuel m rep).
  Proof.
    intros fuel m rep Hrep.
    unfold scc_component_with_fuel.
    apply filter_In. split.
    - exact Hrep.
    - apply connected_stateb_refl.
  Qed.

  Lemma filter_length_le :
    forall {B : Type} (f : B -> bool) xs,
      length (filter f xs) <= length xs.
  Proof.
    intros B f xs.
    induction xs as [| x xs IH]; simpl.
    - lia.
    - destruct (f x); simpl; lia.
  Qed.

  Lemma scc_quotient_loop_covers_work :
    forall loop_fuel reach_fuel (m : @finite_nfa A) work q,
      length work <= loop_fuel ->
      (forall r, In r work -> In r (fnfa_states m)) ->
      In q work ->
      exists c,
        In c (scc_quotient_loop loop_fuel reach_fuel m work) /\
        In q c.
  Proof.
    induction loop_fuel as [| loop_fuel IH];
      intros reach_fuel m work q Hlen Hwork Hq.
    - destruct work; simpl in *; try lia; contradiction.
    - destruct work as [| rep work']; simpl in *; try contradiction.
      destruct Hq as [Hq | Hq].
      + subst q.
        exists (scc_component_with_fuel reach_fuel m rep).
        split; simpl; auto.
        apply scc_component_with_fuel_contains_rep.
        apply Hwork. simpl; auto.
      + destruct
          (state_mem m q (scc_component_with_fuel reach_fuel m rep))
          eqn:Hmem.
        * exists (scc_component_with_fuel reach_fuel m rep).
          split; simpl; auto.
          now apply state_mem_sound in Hmem.
        * destruct
            (IH
               reach_fuel
               m
               (remove_component_states
                  m
                  (scc_component_with_fuel reach_fuel m rep)
                  work')
               q)
            as [c [Hc Hqc]].
          -- eapply Nat.le_trans.
             ++ apply filter_length_le.
             ++ lia.
          -- intros r Hr.
             unfold remove_component_states in Hr.
             apply filter_In in Hr as [Hr _].
             apply Hwork. simpl; auto.
          -- unfold remove_component_states.
             apply filter_In. split; auto.
             rewrite Hmem. reflexivity.
          -- exists c. split; simpl; auto.
  Qed.

  Lemma scc_quotient_with_fuel_covers_states :
    forall reach_fuel (m : @finite_nfa A) q,
      In q (fnfa_states m) ->
      exists c,
        In c (scc_quotient_with_fuel reach_fuel m) /\
        In q c.
  Proof.
    intros reach_fuel m q Hq.
    unfold scc_quotient_with_fuel.
    eapply scc_quotient_loop_covers_work.
    - lia.
    - intros r Hr. exact Hr.
    - exact Hq.
  Qed.

  Lemma finite_path_end_has_scc_component :
    forall reach_fuel (m : @finite_nfa A) p w q,
      fnfa_well_formed m ->
      In p (fnfa_states m) ->
      word_in_alphabet m w ->
      finite_delta_star m p w q ->
      exists c,
        In c (scc_quotient_with_fuel reach_fuel m) /\
        In q c.
  Proof.
    intros reach_fuel m p w q Hwf Hp Hall Hpath.
    apply scc_quotient_with_fuel_covers_states.
    eapply fnfa_well_formed_path_end; eauto.
  Qed.

  Lemma accepting_run_endpoint_has_scc_component :
    forall reach_fuel (m : @finite_nfa A) w r,
      fnfa_well_formed m ->
      word_in_alphabet m w ->
      In r (accepting_run_endpoints m w) ->
      exists c,
        In c (scc_quotient_with_fuel reach_fuel m) /\
        In r c.
  Proof.
    intros reach_fuel m w r Hwf Hall Hr.
    apply scc_quotient_with_fuel_covers_states.
    eapply accepting_run_endpoints_In_states; eauto.
  Qed.

  Lemma scc_quotient_loop_component_sound :
    forall loop_fuel reach_fuel (m : @finite_nfa A) work c,
      In c (scc_quotient_loop loop_fuel reach_fuel m work) ->
      exists rep, c = scc_component_with_fuel reach_fuel m rep.
  Proof.
    induction loop_fuel as [| loop_fuel IH];
      intros reach_fuel m work c H; simpl in H.
    - contradiction.
    - destruct work as [| rep work']; simpl in H; try contradiction.
      destruct H as [H | H].
      + subst c. exists rep. reflexivity.
      + now apply IH in H.
  Qed.

  Lemma scc_quotient_with_fuel_component_connected :
    forall reach_fuel (m : @finite_nfa A) c,
      In c (scc_quotient_with_fuel reach_fuel m) ->
      component_connected m c.
  Proof.
    intros reach_fuel m c H.
    unfold scc_quotient_with_fuel in H.
    apply scc_quotient_loop_component_sound in H as [rep Hc].
    subst c.
    apply scc_component_with_fuel_connected.
  Qed.

  Lemma component_connected_path :
    forall (m : @finite_nfa A) c p q,
      component_connected m c ->
      In p c ->
      In q c ->
      exists w, finite_delta_star m p w q.
  Proof.
    intros m c p q Hconnected Hp Hq.
    destruct (Hconnected p q Hp Hq) as [u [_v [Hpq _Hqp]]].
    exists u. exact Hpq.
  Qed.

  Definition trace_component_aligned
      reach_fuel
      (m : @finite_nfa A)
      (trace : list (finite_state m))
      (walk : list (quotient_component m)) : Prop :=
    length walk = length trace /\
    Forall
      (fun c => In c (scc_quotient_with_fuel reach_fuel m))
      walk /\
    forall k q c,
      nth_error trace k = Some q ->
      nth_error walk k = Some c ->
      In q c.

  Lemma trace_component_aligned_exists :
    forall reach_fuel (m : @finite_nfa A) trace,
      Forall (fun q => In q (fnfa_states m)) trace ->
      exists walk,
        trace_component_aligned reach_fuel m trace walk.
  Proof.
    intros reach_fuel m trace Hall.
    induction Hall as [| q trace Hq _ IH].
    - exists [].
      repeat split; simpl; auto.
      intros k r c Htrace _.
      destruct k; discriminate.
    - destruct (scc_quotient_with_fuel_covers_states reach_fuel m q Hq)
        as [c [Hc Hqc]].
      destruct IH as [walk [Hlen [Hwalk Hallign]]].
      exists (c :: walk).
      split.
      + simpl. now rewrite Hlen.
      + split.
        * constructor; assumption.
        * intros [| k] r d Htrace Hwalk_nth; simpl in *.
          -- inversion Htrace; subst r.
             inversion Hwalk_nth; subst d.
             exact Hqc.
          -- eapply Hallign; eauto.
  Qed.

  Lemma no_EDA_connected_component_choices_unique :
    forall (m : @finite_nfa A) comp q v r c1 c2,
      no_EDA m ->
      component_connected m comp ->
      In q comp ->
      In r comp ->
      finite_useful m q ->
      In c1 (run_choices_between m q v r) ->
      In c2 (run_choices_between m q v r) ->
      c1 = c2.
  Proof.
    intros m comp q v r c1 c2 Hno Hconnected Hq Hr Huseful Hc1 Hc2.
    destruct (component_connected_path m comp r q Hconnected Hr Hq)
      as [u Hreturn].
    eapply no_EDA_same_component_choices_unique; eauto.
  Qed.

  Lemma no_EDA_scc_component_choices_unique :
    forall reach_fuel (m : @finite_nfa A) comp q v r c1 c2,
      no_EDA m ->
      In comp (scc_quotient_with_fuel reach_fuel m) ->
      In q comp ->
      In r comp ->
      finite_useful m q ->
      In c1 (run_choices_between m q v r) ->
      In c2 (run_choices_between m q v r) ->
      c1 = c2.
  Proof.
    intros reach_fuel m comp q v r c1 c2
      Hno Hcomp Hq Hr Huseful Hc1 Hc2.
    eapply no_EDA_connected_component_choices_unique
      with (comp := comp) (q := q) (v := v) (r := r); eauto.
    now apply (scc_quotient_with_fuel_component_connected reach_fuel m comp).
  Qed.

  Lemma no_EDA_scc_run_choices_unique :
    forall reach_fuel (m : @finite_nfa A) comp q v r c1 c2,
      no_EDA m ->
      In comp (scc_quotient_with_fuel reach_fuel m) ->
      In q comp ->
      In r comp ->
      finite_useful m q ->
      run_choices_from (fnfa_base m) q v c1 r ->
      run_choices_from (fnfa_base m) q v c2 r ->
      c1 = c2.
  Proof.
    intros reach_fuel m comp q v r c1 c2
      Hno Hcomp Hq Hr Huseful Hrun1 Hrun2.
    eapply no_EDA_scc_component_choices_unique
      with (reach_fuel := reach_fuel) (comp := comp)
        (q := q) (v := v) (r := r); eauto;
      apply run_choices_between_complete; assumption.
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

  Theorem edab_with_fuel_exponentially_ambiguous :
    forall fuel (m : @finite_nfa A),
      edab_with_fuel fuel m = true ->
      exponentially_ambiguous (fnfa_base m).
  Proof.
    intros fuel m H.
    apply EDA_exponentially_ambiguous.
    now apply edab_with_fuel_sound with (fuel := fuel).
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

  Lemma g5_red_edgeb_sound :
    forall word_fuel (m : @finite_nfa A) c d,
      g5_red_edgeb word_fuel m c d = true ->
      exists p q v,
        In p c /\
        In q d /\
        IDA_pair m p q v.
  Proof.
    intros word_fuel m c d H.
    unfold g5_red_edgeb in H.
    apply existsb_exists in H as [p [Hp Htargets]].
    apply existsb_exists in Htargets as [q [Hq Hpairb]].
    destruct (idab_pairb_sound word_fuel m p q Hpairb) as [v Hpair].
    exists p, q, v. split; [exact Hp | split; [exact Hq | exact Hpair]].
  Qed.

  Lemma g5_plain_edgeb_sound :
    forall graph_fuel (m : @finite_nfa A) c d,
      g5_plain_edgeb graph_fuel m c d = true ->
      exists p q w,
        In p c /\
        In q d /\
        finite_delta_star m p w q.
  Proof.
    intros graph_fuel m c d H.
    unfold g5_plain_edgeb in H.
    apply existsb_exists in H as [p [Hp Htargets]].
    apply existsb_exists in Htargets as [q [Hq Hreach]].
    destruct (reachable_stateb_sound graph_fuel m p q Hreach) as [w Hpath].
    exists p, q, w. split; [exact Hp | split; [exact Hq | exact Hpath]].
  Qed.

  Lemma g5_plain_edgeb_complete_path :
    forall graph_fuel (m : @finite_nfa A) c d p q w,
      In p c ->
      In q d ->
      length w <= graph_fuel ->
      word_in_alphabet m w ->
      finite_delta_star m p w q ->
      g5_plain_edgeb graph_fuel m c d = true.
  Proof.
    intros graph_fuel m c d p q w Hp Hq Hlen Hall Hpath.
    unfold g5_plain_edgeb.
    apply existsb_exists.
    exists p. split; auto.
    apply existsb_exists.
    exists q. split; auto.
    eapply reachable_stateb_complete_path; eauto.
  Qed.

  Lemma g5_edgeb_complete_plain_path :
    forall word_fuel graph_fuel (m : @finite_nfa A) c d p q w,
      In p c ->
      In q d ->
      length w <= graph_fuel ->
      word_in_alphabet m w ->
      finite_delta_star m p w q ->
      g5_edgeb word_fuel graph_fuel m c d = true.
  Proof.
    intros word_fuel graph_fuel m c d p q w Hp Hq Hlen Hall Hpath.
    unfold g5_edgeb.
    apply orb_true_iff. right.
    eapply g5_plain_edgeb_complete_path; eauto.
  Qed.

  Lemma g5_walkb_tail :
    forall word_fuel graph_fuel (m : @finite_nfa A) c walk,
      g5_walkb word_fuel graph_fuel m (c :: walk) = true ->
      g5_walkb word_fuel graph_fuel m walk = true.
  Proof.
    intros word_fuel graph_fuel m c walk H.
    destruct walk as [| d walk']; simpl in *; auto.
    apply andb_true_iff in H as [_ Htail].
    exact Htail.
  Qed.

  Lemma g5_walkb_edge_head :
    forall word_fuel graph_fuel (m : @finite_nfa A) c d walk,
      g5_walkb word_fuel graph_fuel m (c :: d :: walk) = true ->
      g5_edgeb word_fuel graph_fuel m c d = true.
  Proof.
    intros word_fuel graph_fuel m c d walk H.
    simpl in H.
    now apply andb_true_iff in H as [Hedge _].
  Qed.

  Lemma last_nonempty_default_irrelevant :
    forall (B : Type) (xs : list B) d e,
      xs <> [] ->
      last xs d = last xs e.
  Proof.
    intros B xs.
    destruct xs as [| x xs]; intros d e Hnonempty; try contradiction.
    clear Hnonempty.
    revert x d e.
    induction xs as [| y ys IH]; intros x d e; simpl.
    - reflexivity.
    - apply IH.
  Qed.

  Lemma component_walk_for_path :
    forall word_fuel graph_fuel (m : @finite_nfa A) p w q c,
      fnfa_well_formed m ->
      In p (fnfa_states m) ->
      word_in_alphabet m w ->
      finite_delta_star m p w q ->
      In c (scc_quotient_with_fuel graph_fuel m) ->
      In p c ->
      1 <= graph_fuel ->
      exists walk d,
        walk <> [] /\
        Forall
          (fun e => In e (scc_quotient_with_fuel graph_fuel m))
          walk /\
        length walk <= S (length w) /\
        In d (scc_quotient_with_fuel graph_fuel m) /\
        In q d /\
        hd c walk = c /\
        last walk c = d /\
        g5_walkb word_fuel graph_fuel m walk = true.
  Proof.
    intros word_fuel graph_fuel m p w q c Hwf Hp Hall Hpath.
    revert c Hp Hall.
    induction Hpath as [q| p a p' w q Hstep Htail IH];
      intros c Hp Hall Hc Hpc Hfuel.
    - exists [c], c.
      repeat split; simpl; auto; try lia; try discriminate.
    - inversion Hall as [| a' w' Ha Hall_tail]; subst.
      destruct Hwf as [Hstarts Hstep_wf].
      assert (Hp' : In p' (fnfa_states m)).
      {
        eapply Hstep_wf; eauto.
      }
      destruct
        (scc_quotient_with_fuel_covers_states graph_fuel m p' Hp')
        as [d [Hd Hp'd]].
      assert (Hedge : g5_edgeb word_fuel graph_fuel m c d = true).
      {
        eapply g5_edgeb_complete_plain_path
          with (p := p) (q := p') (w := [a]).
        - exact Hpc.
        - exact Hp'd.
        - simpl. lia.
        - constructor; auto.
        - eapply Path_cons.
          + exact Hstep.
          + constructor.
      }
      destruct
        (IH d Hp' Hall_tail Hd Hp'd Hfuel)
        as [walk_tail [e [Hnonempty [Hall_walk [Hlen_walk
          [He [Hqe [Hhd [Hlast Hwalk]]]]]]]]].
      exists (c :: walk_tail), e.
      split.
      + discriminate.
      + split.
        * constructor; assumption.
        * split.
          -- simpl. lia.
          -- split.
             ++ exact He.
             ++ split.
                ** exact Hqe.
                ** split.
                   --- simpl. reflexivity.
                   --- split.
                       +++ destruct walk_tail as [| d0 rest]; try contradiction.
                           simpl in Hhd. subst d0.
                           simpl.
                           destruct rest as [| x xs].
                           *** exact Hlast.
                           *** simpl in Hlast.
                               rewrite (last_nonempty_default_irrelevant
                                 (quotient_component m) (x :: xs) c d).
                               ---- exact Hlast.
                               ---- discriminate.
                       +++ destruct walk_tail as [| d0 rest]; try contradiction.
                           simpl in Hhd. subst d0.
                           simpl. apply andb_true_iff. split; assumption.
  Qed.

  Lemma component_walk_for_accepting_run_endpoint :
    forall word_fuel graph_fuel (m : @finite_nfa A) w qf,
      fnfa_well_formed m ->
      word_in_alphabet m w ->
      In qf (accepting_run_endpoints m w) ->
      1 <= graph_fuel ->
      exists q0 c0 cf walk,
        In q0 (nfa_start (fnfa_base m)) /\
        In c0 (scc_quotient_with_fuel graph_fuel m) /\
        In cf (scc_quotient_with_fuel graph_fuel m) /\
        In q0 c0 /\
        In qf cf /\
        walk <> [] /\
        Forall
          (fun e => In e (scc_quotient_with_fuel graph_fuel m))
          walk /\
        length walk <= S (length w) /\
        hd c0 walk = c0 /\
        last walk c0 = cf /\
        g5_walkb word_fuel graph_fuel m walk = true /\
        nfa_final (fnfa_base m) qf = true.
  Proof.
    intros word_fuel graph_fuel m w qf Hwf Hall Hendpoint Hfuel.
    destruct (accepting_run_endpoints_In m w qf Hendpoint)
      as [q0 [Hstart [Hpath Hfinal]]].
    destruct Hwf as [Hstarts Hstep_wf].
    assert (Hq0_states : In q0 (fnfa_states m)).
    {
      apply Hstarts. exact Hstart.
    }
    destruct
      (scc_quotient_with_fuel_covers_states graph_fuel m q0 Hq0_states)
      as [c0 [Hc0 Hq0c0]].
    destruct
      (component_walk_for_path
         word_fuel
         graph_fuel
         m
         q0
         w
          qf
          c0)
      as [walk [cf [Hnonempty [Hall_walk [Hlen_walk
        [Hcf [Hqfcf [Hhd [Hlast Hwalk]]]]]]]]].
    - split; eauto.
    - exact Hq0_states.
    - exact Hall.
    - exact Hpath.
    - exact Hc0.
    - exact Hq0c0.
    - exact Hfuel.
    - exists q0, c0, cf, walk.
      repeat split; assumption.
  Qed.

  Lemma component_walk_for_accepting_run_occurrence :
    forall word_fuel graph_fuel (m : @finite_nfa A) w i,
      fnfa_well_formed m ->
      word_in_alphabet m w ->
      i < length (accepting_run_endpoints m w) ->
      1 <= graph_fuel ->
      exists qf q0 c0 cf walk,
        nth_error (accepting_run_endpoints m w) i = Some qf /\
        In q0 (nfa_start (fnfa_base m)) /\
        In c0 (scc_quotient_with_fuel graph_fuel m) /\
        In cf (scc_quotient_with_fuel graph_fuel m) /\
        In q0 c0 /\
        In qf cf /\
        walk <> [] /\
        Forall
          (fun e => In e (scc_quotient_with_fuel graph_fuel m))
          walk /\
        length walk <= S (length w) /\
        hd c0 walk = c0 /\
        last walk c0 = cf /\
        g5_walkb word_fuel graph_fuel m walk = true /\
        nfa_final (fnfa_base m) qf = true.
  Proof.
    intros word_fuel graph_fuel m w i Hwf Hall Hi Hfuel.
    destruct
      (nth_error_exists_lt (accepting_run_endpoints m w) i Hi)
      as [qf Hqf].
    destruct (nth_error_In_lt (accepting_run_endpoints m w) i qf Hqf)
      as [Hendpoint _].
    destruct
      (component_walk_for_accepting_run_endpoint
        word_fuel graph_fuel m w qf Hwf Hall Hendpoint Hfuel)
      as [q0 [c0 [cf [walk Hwalk_data]]]].
    exists qf, q0, c0, cf, walk.
    repeat split; try exact Hqf; tauto.
  Qed.

  Lemma g5_red_pathb_from_complete_walk :
    forall path_fuel word_fuel graph_fuel
        (m : @finite_nfa A) components c walk red_count,
      length walk <= path_fuel ->
      Forall (fun d => In d components) walk ->
      g5_walkb_from word_fuel graph_fuel m c walk = true ->
      red_count <= g5_red_edges_on_walk_from word_fuel m c walk ->
      g5_red_pathb_from
        path_fuel word_fuel graph_fuel m components red_count c = true.
  Proof.
    induction path_fuel as [| path_fuel IH];
      intros word_fuel graph_fuel m components c walk red_count
        Hlen Hall Hwalk Hred.
    - destruct red_count as [| red_count']; simpl; auto.
      destruct walk as [| d walk]; simpl in *; lia.
    - destruct red_count as [| red_count']; simpl; auto.
      destruct walk as [| d walk'].
      + simpl in Hred. lia.
      + simpl in Hwalk.
        apply andb_true_iff in Hwalk as [Hedge Hwalk_tail].
        inversion Hall as [| d' walk'' Hd Hall_tail]; subst.
        apply existsb_exists.
        exists d. split; auto.
        rewrite Hedge.
        simpl in Hlen.
        simpl in Hred.
        destruct (g5_red_edgeb word_fuel m c d) eqn:Hred_edge.
        * apply (IH word_fuel graph_fuel m components d walk' red_count').
          -- lia.
          -- exact Hall_tail.
          -- exact Hwalk_tail.
          -- lia.
        * apply (IH word_fuel graph_fuel m components d walk' (S red_count')).
          -- lia.
          -- exact Hall_tail.
          -- exact Hwalk_tail.
          -- lia.
  Qed.

  Lemma g5_red_pathb_with_fuel_complete_walk :
    forall word_fuel graph_fuel (m : @finite_nfa A) walk red_count,
      let components := scc_quotient_with_fuel graph_fuel m in
      walk <> [] ->
      length walk <= S (length components) ->
      Forall (fun d => In d components) walk ->
      g5_walkb word_fuel graph_fuel m walk = true ->
      red_count <= g5_red_edges_on_walk word_fuel m walk ->
      g5_red_pathb_with_fuel word_fuel graph_fuel m red_count = true.
  Proof.
    intros word_fuel graph_fuel m walk red_count components
      Hnonempty Hlen Hall Hwalk Hred.
    destruct red_count as [| red_count']; simpl; auto.
    unfold g5_red_pathb_with_fuel.
    fold components.
    destruct walk as [| c walk']; try contradiction.
    inversion Hall as [| c' walk'' Hc Hall_tail]; subst.
    apply existsb_exists.
    exists c. split; auto.
    apply (g5_red_pathb_from_complete_walk
      (length components) word_fuel graph_fuel m components c walk'
      (S red_count')).
    - simpl in Hlen. lia.
    - exact Hall_tail.
    - exact Hwalk.
    - exact Hred.
  Qed.

  Lemma g5_red_pathb_false_bounds_walk :
    forall word_fuel graph_fuel (m : @finite_nfa A) walk k,
      let components := scc_quotient_with_fuel graph_fuel m in
      g5_red_pathb_with_fuel word_fuel graph_fuel m (S k) = false ->
      walk <> [] ->
      length walk <= S (length components) ->
      Forall (fun d => In d components) walk ->
      g5_walkb word_fuel graph_fuel m walk = true ->
      g5_red_edges_on_walk word_fuel m walk <= k.
  Proof.
    intros word_fuel graph_fuel m walk k components
      Hchecker Hnonempty Hlen Hall Hwalk.
    destruct
      (le_gt_dec
         (S k)
         (g5_red_edges_on_walk word_fuel m walk))
      as [Hmany | Hfew].
    - pose proof
        (g5_red_pathb_with_fuel_complete_walk
           word_fuel graph_fuel m walk (S k)
           Hnonempty Hlen Hall Hwalk Hmany)
        as Htrue.
      rewrite Hchecker in Htrue. discriminate.
    - lia.
  Qed.

  Lemma accepting_run_endpoint_component_walk_red_bound :
    forall word_fuel graph_fuel (m : @finite_nfa A) w qf k,
      let components := scc_quotient_with_fuel graph_fuel m in
      fnfa_well_formed m ->
      word_in_alphabet m w ->
      In qf (accepting_run_endpoints m w) ->
      1 <= graph_fuel ->
      length w <= length components ->
      g5_red_pathb_with_fuel word_fuel graph_fuel m (S k) = false ->
      exists q0 c0 cf walk,
        In q0 (nfa_start (fnfa_base m)) /\
        In c0 components /\
        In cf components /\
        In q0 c0 /\
        In qf cf /\
        walk <> [] /\
        Forall (fun e => In e components) walk /\
        length walk <= S (length w) /\
        hd c0 walk = c0 /\
        last walk c0 = cf /\
        g5_walkb word_fuel graph_fuel m walk = true /\
        g5_red_edges_on_walk word_fuel m walk <= k /\
        nfa_final (fnfa_base m) qf = true.
  Proof.
    intros word_fuel graph_fuel m w qf k components
      Hwf Hall Hendpoint Hfuel Hlen_word Hchecker.
    destruct
      (component_walk_for_accepting_run_endpoint
         word_fuel graph_fuel m w qf Hwf Hall Hendpoint Hfuel)
      as [q0 [c0 [cf [walk Hwalk_data]]]].
    destruct Hwalk_data as [Hstart Hwalk_data].
    destruct Hwalk_data as [Hc0 Hwalk_data].
    destruct Hwalk_data as [Hcf Hwalk_data].
    destruct Hwalk_data as [Hq0c0 Hwalk_data].
    destruct Hwalk_data as [Hqfcf Hwalk_data].
    destruct Hwalk_data as [Hnonempty Hwalk_data].
    destruct Hwalk_data as [Hall_walk Hwalk_data].
    destruct Hwalk_data as [Hlen_walk Hwalk_data].
    destruct Hwalk_data as [Hhd Hwalk_data].
    destruct Hwalk_data as [Hlast Hwalk_data].
    destruct Hwalk_data as [Hwalk Hfinal].
    assert (Hlen_walk_short : length walk <= S (length components)) by lia.
    pose proof
      (g5_red_pathb_false_bounds_walk
         word_fuel graph_fuel m walk k
         Hchecker Hnonempty Hlen_walk_short Hall_walk Hwalk)
      as Hred_bound.
    exists q0, c0, cf, walk.
    repeat split; assumption.
  Qed.

  Lemma max_g5_red_depth_with_fuel_next_false :
    forall word_fuel graph_fuel (m : @finite_nfa A) max_d k,
      max_g5_red_depth_with_fuel word_fuel graph_fuel m max_d = k ->
      k < max_d ->
      g5_red_pathb_with_fuel word_fuel graph_fuel m (S k) = false.
  Proof.
    intros word_fuel graph_fuel m max_d.
    induction max_d as [| max_d IH]; intros k Hmax Hlt.
    - lia.
    - change
        ((if g5_red_pathb_with_fuel word_fuel graph_fuel m (S max_d)
          then S max_d
          else max_g5_red_depth_with_fuel word_fuel graph_fuel m max_d) = k)
        in Hmax.
      destruct (g5_red_pathb_with_fuel word_fuel graph_fuel m (S max_d))
        eqn:Hhit.
      + subst k. lia.
      + destruct (Nat.eq_dec k max_d) as [Heq | Hneq].
        * rewrite Heq. exact Hhit.
        * apply IH.
          -- exact Hmax.
          -- lia.
  Qed.

  Lemma accepting_run_endpoint_component_walk_red_bound_from_max :
    forall word_fuel graph_fuel (m : @finite_nfa A) w qf k,
      let components := scc_quotient_with_fuel graph_fuel m in
      fnfa_well_formed m ->
      word_in_alphabet m w ->
      In qf (accepting_run_endpoints m w) ->
      1 <= graph_fuel ->
      length w <= length components ->
      max_g5_red_depth_with_fuel
        word_fuel graph_fuel m (length components) = k ->
      k < length components ->
      exists q0 c0 cf walk,
        In q0 (nfa_start (fnfa_base m)) /\
        In c0 components /\
        In cf components /\
        In q0 c0 /\
        In qf cf /\
        walk <> [] /\
        Forall (fun e => In e components) walk /\
        length walk <= S (length w) /\
        hd c0 walk = c0 /\
        last walk c0 = cf /\
        g5_walkb word_fuel graph_fuel m walk = true /\
        g5_red_edges_on_walk word_fuel m walk <= k /\
        nfa_final (fnfa_base m) qf = true.
  Proof.
    intros word_fuel graph_fuel m w qf k components
      Hwf Hall Hendpoint Hfuel Hlen_word Hmax Hlt.
    eapply accepting_run_endpoint_component_walk_red_bound; eauto.
    eapply max_g5_red_depth_with_fuel_next_false; eauto.
  Qed.

  Lemma accepting_run_occurrence_component_walk_red_bound_from_max :
    forall word_fuel graph_fuel (m : @finite_nfa A) w i k,
      let components := scc_quotient_with_fuel graph_fuel m in
      fnfa_well_formed m ->
      word_in_alphabet m w ->
      i < length (accepting_run_endpoints m w) ->
      1 <= graph_fuel ->
      length w <= length components ->
      max_g5_red_depth_with_fuel
        word_fuel graph_fuel m (length components) = k ->
      k < length components ->
      exists qf q0 c0 cf walk,
        nth_error (accepting_run_endpoints m w) i = Some qf /\
        In q0 (nfa_start (fnfa_base m)) /\
        In c0 components /\
        In cf components /\
        In q0 c0 /\
        In qf cf /\
        walk <> [] /\
        Forall (fun e => In e components) walk /\
        length walk <= S (length w) /\
        hd c0 walk = c0 /\
        last walk c0 = cf /\
        g5_walkb word_fuel graph_fuel m walk = true /\
        g5_red_edges_on_walk word_fuel m walk <= k /\
        nfa_final (fnfa_base m) qf = true.
  Proof.
    intros word_fuel graph_fuel m w i k components
      Hwf Hall Hi Hfuel Hlen_word Hmax Hlt.
    destruct
      (nth_error_exists_lt (accepting_run_endpoints m w) i Hi)
      as [qf Hqf].
    destruct (nth_error_In_lt (accepting_run_endpoints m w) i qf Hqf)
      as [Hendpoint _].
    destruct
      (accepting_run_endpoint_component_walk_red_bound_from_max
        word_fuel graph_fuel m w qf k
        Hwf Hall Hendpoint Hfuel Hlen_word Hmax Hlt)
      as [q0 [c0 [cf [walk Hwalk_data]]]].
    exists qf, q0, c0, cf, walk.
    repeat split; try exact Hqf; tauto.
  Qed.

  Lemma component_walk_for_accepting_run_full_choice :
    forall word_fuel graph_fuel (m : @finite_nfa A) w i,
      fnfa_well_formed m ->
      word_in_alphabet m w ->
      i < length (accepting_run_full_choices m w) ->
      1 <= graph_fuel ->
      exists choices start_idx tail q0 qf c0 cf walk,
        nth_error (accepting_run_full_choices m w) i = Some choices /\
        choices = start_idx :: tail /\
        nth_error (nfa_start (fnfa_base m)) start_idx = Some q0 /\
        run_choices_from (fnfa_base m) q0 w tail qf /\
        In c0 (scc_quotient_with_fuel graph_fuel m) /\
        In cf (scc_quotient_with_fuel graph_fuel m) /\
        In q0 c0 /\
        In qf cf /\
        walk <> [] /\
        Forall
          (fun e => In e (scc_quotient_with_fuel graph_fuel m))
          walk /\
        length walk <= S (length w) /\
        hd c0 walk = c0 /\
        last walk c0 = cf /\
        g5_walkb word_fuel graph_fuel m walk = true /\
        nfa_final (fnfa_base m) qf = true.
  Proof.
    intros word_fuel graph_fuel m w i Hwf Hall Hi Hfuel.
    destruct
      (nth_error_exists_lt (accepting_run_full_choices m w) i Hi)
      as [choices Hchoices].
    destruct
      (nth_error_In_lt (accepting_run_full_choices m w) i choices Hchoices)
      as [Hchoices_in _].
    destruct
      (accepting_run_full_choices_In_choices m w choices Hchoices_in)
      as [start_idx [q0 [tail [qf
        [Hchoices_eq [Hstart_nth [Hrun Hfinal]]]]]]].
    assert (Hstart_in : In q0 (nfa_start (fnfa_base m))).
    {
      eapply nth_error_In. exact Hstart_nth.
    }
    assert (Hpath : finite_delta_star m q0 w qf).
    {
      now apply run_choices_from_path with (choices := tail).
    }
    destruct Hwf as [Hstarts Hstep_wf].
    assert (Hq0_states : In q0 (fnfa_states m)).
    {
      apply Hstarts. exact Hstart_in.
    }
    destruct
      (scc_quotient_with_fuel_covers_states graph_fuel m q0 Hq0_states)
      as [c0 [Hc0 Hq0c0]].
    destruct
      (component_walk_for_path
        word_fuel graph_fuel m q0 w qf c0)
      as [walk [cf [Hnonempty [Hall_walk [Hlen_walk
        [Hcf [Hqfcf [Hhd [Hlast Hwalk]]]]]]]]].
    - split; eauto.
    - exact Hq0_states.
    - exact Hall.
    - exact Hpath.
    - exact Hc0.
    - exact Hq0c0.
    - exact Hfuel.
    - exists choices, start_idx, tail, q0, qf, c0, cf, walk.
      repeat split; assumption.
  Qed.

  Lemma accepting_run_full_choice_replay_trace :
    forall (m : @finite_nfa A) w i,
      i < length (accepting_run_full_choices m w) ->
      exists choices start_idx tail q0 qf trace,
        nth_error (accepting_run_full_choices m w) i = Some choices /\
        choices = start_idx :: tail /\
        nth_error (nfa_start (fnfa_base m)) start_idx = Some q0 /\
        run_choices_from (fnfa_base m) q0 w tail qf /\
        nfa_final (fnfa_base m) qf = true /\
        replay_choices_from (fnfa_base m) q0 w tail = Some trace /\
        run_trace_from (fnfa_base m) q0 w qf trace /\
        length trace = S (length w).
  Proof.
    intros m w i Hi.
    destruct
      (nth_error_exists_lt (accepting_run_full_choices m w) i Hi)
      as [choices Hchoices].
    destruct
      (nth_error_In_lt (accepting_run_full_choices m w) i choices Hchoices)
      as [Hchoices_in _].
    destruct
      (accepting_run_full_choices_In_choices m w choices Hchoices_in)
      as [start_idx [q0 [tail [qf
        [Hchoices_eq [Hstart_nth [Hrun Hfinal]]]]]]].
    destruct
      (replay_choices_from_run_choices
        (fnfa_base m) q0 w tail qf Hrun)
      as [trace [Hreplay Htrace]].
    exists choices, start_idx, tail, q0, qf, trace.
    repeat split; try assumption.
    now apply run_trace_from_length in Htrace.
  Qed.

  Lemma full_choice_same_replay_trace_unique :
    forall (m : @finite_nfa A) w
      start_idx1 start_idx2 tail1 tail2 q01 q02 trace,
      fnfa_choice_nodup m ->
      nth_error (nfa_start (fnfa_base m)) start_idx1 = Some q01 ->
      nth_error (nfa_start (fnfa_base m)) start_idx2 = Some q02 ->
      length tail1 = length w ->
      length tail2 = length w ->
      replay_choices_from (fnfa_base m) q01 w tail1 = Some trace ->
      replay_choices_from (fnfa_base m) q02 w tail2 = Some trace ->
      start_idx1 :: tail1 = start_idx2 :: tail2.
  Proof.
    intros m w start_idx1 start_idx2 tail1 tail2 q01 q02 trace
      [Hstart_nodup Hstep_nodup]
      Hstart1 Hstart2 Hlen1 Hlen2 Hreplay1 Hreplay2.
    destruct
      (replay_choices_from_starts_with
        (fnfa_base m) q01 w tail1 trace Hreplay1)
      as [trace_tail1 Htrace1].
    destruct
      (replay_choices_from_starts_with
        (fnfa_base m) q02 w tail2 trace Hreplay2)
      as [trace_tail2 Htrace2].
    rewrite Htrace1 in Htrace2.
    injection Htrace2 as Hq Htail_trace.
    subst q02.
    assert (Hstart_idx : start_idx1 = start_idx2).
    {
      eapply nth_error_NoDup_eq; eauto.
    }
    subst start_idx2.
    f_equal.
    eapply replay_choices_from_unique_with_nodup_steps; eauto.
  Qed.

  Lemma accepting_run_full_choice_same_replay_trace_equal_choices :
    forall (m : @finite_nfa A) w i j trace,
      fnfa_choice_nodup m ->
      i < length (accepting_run_full_choices m w) ->
      j < length (accepting_run_full_choices m w) ->
      (exists choices start_idx tail q0 qf,
        nth_error (accepting_run_full_choices m w) i = Some choices /\
        choices = start_idx :: tail /\
        nth_error (nfa_start (fnfa_base m)) start_idx = Some q0 /\
        run_choices_from (fnfa_base m) q0 w tail qf /\
        nfa_final (fnfa_base m) qf = true /\
        replay_choices_from (fnfa_base m) q0 w tail = Some trace) ->
      (exists choices start_idx tail q0 qf,
        nth_error (accepting_run_full_choices m w) j = Some choices /\
        choices = start_idx :: tail /\
        nth_error (nfa_start (fnfa_base m)) start_idx = Some q0 /\
        run_choices_from (fnfa_base m) q0 w tail qf /\
        nfa_final (fnfa_base m) qf = true /\
        replay_choices_from (fnfa_base m) q0 w tail = Some trace) ->
      exists choices,
        nth_error (accepting_run_full_choices m w) i = Some choices /\
        nth_error (accepting_run_full_choices m w) j = Some choices.
  Proof.
    intros m w i j trace Hnodup Hi Hj Hrun_i Hrun_j.
    destruct Hrun_i as
      (choices_i & start_i & tail_i & q0_i & qf_i &
        Hnth_i & Hchoices_i & Hstart_i & Hrun_i & _Hfinal_i & Hreplay_i).
    destruct Hrun_j as
      (choices_j & start_j & tail_j & q0_j & qf_j &
        Hnth_j & Hchoices_j & Hstart_j & Hrun_j & _Hfinal_j & Hreplay_j).
    assert (Htail_len_i : length tail_i = length w).
    {
      now apply run_choices_from_length in Hrun_i.
    }
    assert (Htail_len_j : length tail_j = length w).
    {
      now apply run_choices_from_length in Hrun_j.
    }
    assert (Hchoices_eq : choices_i = choices_j).
    {
      subst choices_i choices_j.
      eapply full_choice_same_replay_trace_unique; eauto.
    }
    subst choices_j.
    exists choices_i.
    split.
    - exact Hnth_i.
    - now rewrite Hchoices_eq.
  Qed.

  Lemma accepting_run_full_choice_component_walk_red_bound_from_max :
    forall word_fuel graph_fuel (m : @finite_nfa A) w i k,
      let components := scc_quotient_with_fuel graph_fuel m in
      fnfa_well_formed m ->
      word_in_alphabet m w ->
      i < length (accepting_run_full_choices m w) ->
      1 <= graph_fuel ->
      length w <= length components ->
      max_g5_red_depth_with_fuel
        word_fuel graph_fuel m (length components) = k ->
      k < length components ->
      exists choices start_idx tail q0 qf c0 cf walk,
        nth_error (accepting_run_full_choices m w) i = Some choices /\
        choices = start_idx :: tail /\
        nth_error (nfa_start (fnfa_base m)) start_idx = Some q0 /\
        run_choices_from (fnfa_base m) q0 w tail qf /\
        In c0 components /\
        In cf components /\
        In q0 c0 /\
        In qf cf /\
        walk <> [] /\
        Forall (fun e => In e components) walk /\
        length walk <= S (length w) /\
        hd c0 walk = c0 /\
        last walk c0 = cf /\
        g5_walkb word_fuel graph_fuel m walk = true /\
        g5_red_edges_on_walk word_fuel m walk <= k /\
        nfa_final (fnfa_base m) qf = true.
  Proof.
    intros word_fuel graph_fuel m w i k components
      Hwf Hall Hi Hfuel Hlen_word Hmax Hlt.
    destruct
      (component_walk_for_accepting_run_full_choice
        word_fuel graph_fuel m w i Hwf Hall Hi Hfuel)
      as [choices [start_idx [tail [q0 [qf [c0 [cf [walk Hdata]]]]]]]].
    destruct Hdata as [Hchoices Hdata].
    destruct Hdata as [Hchoices_eq Hdata].
    destruct Hdata as [Hstart_nth Hdata].
    destruct Hdata as [Hrun Hdata].
    destruct Hdata as [Hc0 Hdata].
    destruct Hdata as [Hcf Hdata].
    destruct Hdata as [Hq0c0 Hdata].
    destruct Hdata as [Hqfcf Hdata].
    destruct Hdata as [Hnonempty Hdata].
    destruct Hdata as [Hall_walk Hdata].
    destruct Hdata as [Hlen_walk Hdata].
    destruct Hdata as [Hhd Hdata].
    destruct Hdata as [Hlast Hdata].
    destruct Hdata as [Hwalk Hfinal].
    assert (Hchecker :
      g5_red_pathb_with_fuel word_fuel graph_fuel m (S k) = false).
    {
      eapply max_g5_red_depth_with_fuel_next_false; eauto.
    }
    assert (Hlen_walk_short : length walk <= S (length components)) by lia.
    pose proof
      (g5_red_pathb_false_bounds_walk
         word_fuel graph_fuel m walk k
         Hchecker Hnonempty Hlen_walk_short Hall_walk Hwalk)
      as Hred_bound.
    exists choices, start_idx, tail, q0, qf, c0, cf, walk.
    repeat split; assumption.
  Qed.

  Definition full_choice_g5_witness_bound
      (word_fuel graph_fuel : nat)
      (m : @finite_nfa A)
      (k : nat) : Prop :=
    let components := scc_quotient_with_fuel graph_fuel m in
    fnfa_well_formed m /\
    1 <= graph_fuel /\
    max_g5_red_depth_with_fuel
      word_fuel graph_fuel m (length components) = k /\
    k < length components.

  Definition full_choice_g5_witness_bound_le
      (word_fuel graph_fuel : nat)
      (m : @finite_nfa A)
      (k : nat) : Prop :=
    let components := scc_quotient_with_fuel graph_fuel m in
    fnfa_well_formed m /\
    1 <= graph_fuel /\
    max_g5_red_depth_with_fuel
      word_fuel graph_fuel m (length components) = k /\
    k <= length components.

  Lemma full_choice_g5_witness_bound_le_from_max :
    forall word_fuel graph_fuel (m : @finite_nfa A) k,
      fnfa_well_formed m ->
      1 <= graph_fuel ->
      max_g5_red_depth_with_fuel
        word_fuel graph_fuel m
        (length (scc_quotient_with_fuel graph_fuel m)) = k ->
      full_choice_g5_witness_bound_le word_fuel graph_fuel m k.
  Proof.
    intros word_fuel graph_fuel m k Hwf Hfuel Hmax.
    unfold full_choice_g5_witness_bound_le.
    split.
    - exact Hwf.
    - split.
      + exact Hfuel.
      + split.
        * exact Hmax.
        * rewrite <- Hmax.
          apply max_g5_red_depth_with_fuel_le.
  Qed.

  Lemma full_choice_g5_witnesses_from_max :
    forall word_fuel graph_fuel (m : @finite_nfa A) k w,
      let components := scc_quotient_with_fuel graph_fuel m in
      full_choice_g5_witness_bound word_fuel graph_fuel m k ->
      word_in_alphabet m w ->
      length w <= length components ->
      forall i,
        i < length (accepting_run_full_choices m w) ->
        exists walk,
          g5_walkb word_fuel graph_fuel m walk = true /\
          g5_red_edges_on_walk word_fuel m walk <= k /\
          length walk <= S (length w).
  Proof.
    intros word_fuel graph_fuel m k w components
      [Hwf [Hfuel [Hmax Hlt]]] Hall Hlen_word i Hi.
    destruct
      (accepting_run_full_choice_component_walk_red_bound_from_max
        word_fuel graph_fuel m w i k
        Hwf Hall Hi Hfuel Hlen_word Hmax Hlt)
      as [choices [start_idx [tail [q0 [qf [c0 [cf [walk Hdata]]]]]]]].
    destruct Hdata as [_ Hdata].
    destruct Hdata as [_ Hdata].
    destruct Hdata as [_ Hdata].
    destruct Hdata as [_ Hdata].
    destruct Hdata as [_ Hdata].
    destruct Hdata as [_ Hdata].
    destruct Hdata as [_ Hdata].
    destruct Hdata as [_ Hdata].
    destruct Hdata as [_ Hdata].
    destruct Hdata as [_ Hdata].
    destruct Hdata as [Hlen_walk Hdata].
    destruct Hdata as [_ Hdata].
    destruct Hdata as [_ Hdata].
    destruct Hdata as [Hwalk Hdata].
    destruct Hdata as [Hred _].
    exists walk.
    repeat split; assumption.
  Qed.

  Lemma full_choice_g5_witnesses_from_max_le :
    forall word_fuel graph_fuel (m : @finite_nfa A) k w,
      let components := scc_quotient_with_fuel graph_fuel m in
      full_choice_g5_witness_bound_le word_fuel graph_fuel m k ->
      word_in_alphabet m w ->
      length w <= length components ->
      forall i,
        i < length (accepting_run_full_choices m w) ->
        exists walk,
          g5_walkb word_fuel graph_fuel m walk = true /\
          g5_red_edges_on_walk word_fuel m walk <= k /\
          length walk <= S (length w).
  Proof.
    intros word_fuel graph_fuel m k w components
      [Hwf [Hfuel [Hmax Hle]]] Hall Hlen_word i Hi.
    destruct (Nat.eq_dec k (length components)) as [Heq | Hneq].
    - destruct
        (component_walk_for_accepting_run_full_choice
          word_fuel graph_fuel m w i Hwf Hall Hi Hfuel)
        as [choices [start_idx [tail [q0 [qf [c0 [cf [walk Hdata]]]]]]]].
      destruct Hdata as [_ Hdata].
      destruct Hdata as [_ Hdata].
      destruct Hdata as [_ Hdata].
      destruct Hdata as [_ Hdata].
      destruct Hdata as [_ Hdata].
      destruct Hdata as [_ Hdata].
      destruct Hdata as [_ Hdata].
      destruct Hdata as [_ Hdata].
      destruct Hdata as [_ Hdata].
      destruct Hdata as [_ Hdata].
      destruct Hdata as [Hlen_walk Hdata].
      destruct Hdata as [_ Hdata].
      destruct Hdata as [_ Hdata].
      destruct Hdata as [Hwalk _].
      exists walk. repeat split; auto.
      pose proof (g5_red_edges_on_walk_le_edges word_fuel m walk) as Hred.
      assert (Hpred : pred (length walk) <= length w).
      {
        destruct (length walk); simpl in *; lia.
      }
      rewrite Heq.
      eapply Nat.le_trans.
      + exact Hred.
      + eapply Nat.le_trans; [exact Hpred | exact Hlen_word].
    - eapply full_choice_g5_witnesses_from_max; eauto.
      split.
      + exact Hwf.
      + split.
        * exact Hfuel.
        * split.
          -- exact Hmax.
          -- assert (Hle_components : k <= length components) by exact Hle.
             apply Nat.lt_eq_cases in Hle_components as [Hlt | Heq].
             ++ exact Hlt.
             ++ contradiction.
  Qed.

  Lemma finite_index_choice_list :
    forall (X : Type) n (P : nat -> X -> Prop),
      (forall i, i < n -> exists x, P i x) ->
      exists xs,
        length xs = n /\
        forall i,
          i < n ->
          exists x, nth_error xs i = Some x /\ P i x.
  Proof.
    intros X n.
    induction n as [| n IH]; intros P Hchoice.
    - exists []. split; simpl; auto.
      intros i Hi. lia.
    - destruct (Hchoice 0) as [x0 Hx0]; [lia|].
      destruct
        (IH
          (fun i x => P (S i) x))
        as [xs [Hlen Hxs]].
      {
        intros i Hi.
        apply Hchoice. lia.
      }
      exists (x0 :: xs). split.
      + simpl. lia.
      + intros i Hi.
        destruct i as [| i].
        * exists x0. simpl. auto.
        * destruct (Hxs i) as [x [Hnth HP]]; [lia|].
          exists x. simpl. auto.
  Qed.

  Definition accepting_run_g5_walk_witnesses_on_alphabet
      (word_fuel : nat)
      (m : @finite_nfa A)
      (d : nat) : Prop :=
    forall w,
      word_in_alphabet m w ->
      exists walk_of : nat -> list (quotient_component m),
        forall i,
          i < length (accepting_run_full_choices m w) ->
          g5_red_edges_on_walk word_fuel m (walk_of i) <= d /\
          length (walk_of i) <= S (length w).

  Definition accepting_run_g5_payload_injection_on_alphabet
      (word_fuel : nat)
      (m : @finite_nfa A)
      (Payload : Type)
      (payloads : list Payload)
      (d : nat) : Prop :=
    forall w,
      word_in_alphabet m w ->
      forall walk_of : nat -> list (quotient_component m),
        (forall i,
          i < length (accepting_run_full_choices m w) ->
          g5_red_edges_on_walk word_fuel m (walk_of i) <= d /\
          length (walk_of i) <= S (length w)) ->
        exists payload_of : nat -> Payload,
          (forall i,
            i < length (accepting_run_full_choices m w) ->
            In (payload_of i) payloads) /\
          (forall i j,
            i < length (accepting_run_full_choices m w) ->
            j < length (accepting_run_full_choices m w) ->
            (g5_red_position_vector d word_fuel m (walk_of i),
              payload_of i) =
            (g5_red_position_vector d word_fuel m (walk_of j),
            payload_of j) ->
            i = j).

  Definition accepting_run_g5_payload_function_on_alphabet
      (word_fuel : nat)
      (m : @finite_nfa A)
      (Payload : Type)
      (payloads : list Payload)
      (d : nat) : Prop :=
    forall w,
      word_in_alphabet m w ->
      forall walk_of : nat -> list (quotient_component m),
        (forall i,
          i < length (accepting_run_full_choices m w) ->
          g5_red_edges_on_walk word_fuel m (walk_of i) <= d /\
          length (walk_of i) <= S (length w)) ->
        exists payload_of : nat -> Payload,
          (forall i,
            i < length (accepting_run_full_choices m w) ->
            In (payload_of i) payloads) /\
          (forall i j,
            i < length (accepting_run_full_choices m w) ->
            j < length (accepting_run_full_choices m w) ->
            g5_red_position_vector d word_fuel m (walk_of i) =
            g5_red_position_vector d word_fuel m (walk_of j) ->
            payload_of i = payload_of j ->
            i = j).

  Definition state_pair_payload_bound (m : @finite_nfa A) : nat :=
    S (length (fnfa_states m) * length (fnfa_states m)).

  Definition accepting_run_g5_boundary_index_payload_function_on_alphabet
      (word_fuel : nat)
      (m : @finite_nfa A)
      (d : nat) : Prop :=
    forall w,
      word_in_alphabet m w ->
      forall walk_of : nat -> list (quotient_component m),
        (forall i,
          i < length (accepting_run_full_choices m w) ->
          g5_red_edges_on_walk word_fuel m (walk_of i) <= d /\
          length (walk_of i) <= S (length w)) ->
        exists payload_of : nat -> list nat,
          (forall i,
            i < length (accepting_run_full_choices m w) ->
            In (payload_of i)
              (nat_vectors_below (S d) (state_pair_payload_bound m))) /\
          (forall i j,
            i < length (accepting_run_full_choices m w) ->
            j < length (accepting_run_full_choices m w) ->
            g5_red_position_vector d word_fuel m (walk_of i) =
            g5_red_position_vector d word_fuel m (walk_of j) ->
            payload_of i = payload_of j ->
            i = j).

  Definition accepting_run_g5_positive_boundary_index_payload_function_on_alphabet
      (word_fuel : nat)
      (m : @finite_nfa A)
      (d : nat) : Prop :=
    forall w,
      word_in_alphabet m w ->
      forall walk_of : nat -> list (quotient_component m),
        (forall i,
          i < length (accepting_run_full_choices m w) ->
          g5_red_edges_on_walk word_fuel m (walk_of i) <= d /\
          length (walk_of i) <= S (length w)) ->
        exists payload_of : nat -> list nat,
          (forall i,
            i < length (accepting_run_full_choices m w) ->
            In (payload_of i)
              (nat_vectors_below (S d) (S (state_pair_payload_bound m)))) /\
          (forall i j,
            i < length (accepting_run_full_choices m w) ->
            j < length (accepting_run_full_choices m w) ->
            g5_red_position_vector d word_fuel m (walk_of i) =
            g5_red_position_vector d word_fuel m (walk_of j) ->
            payload_of i = payload_of j ->
            i = j).

  Lemma accepting_run_g5_payload_function_from_boundary_indices :
    forall word_fuel (m : @finite_nfa A) d,
      accepting_run_g5_boundary_index_payload_function_on_alphabet
        word_fuel m d ->
      accepting_run_g5_payload_function_on_alphabet
        word_fuel m
        (list nat)
        (nat_vectors_below (S d) (state_pair_payload_bound m))
        d.
  Proof.
    intros word_fuel m d Hpayload w Hall walk_of Hwalks.
    exact (Hpayload w Hall walk_of Hwalks).
  Qed.

  Lemma accepting_run_g5_payload_function_from_positive_boundary_indices :
    forall word_fuel (m : @finite_nfa A) d,
      accepting_run_g5_positive_boundary_index_payload_function_on_alphabet
        word_fuel m d ->
      accepting_run_g5_payload_function_on_alphabet
        word_fuel m
        (list nat)
        (nat_vectors_below (S d) (S (state_pair_payload_bound m)))
        d.
  Proof.
    intros word_fuel m d Hpayload w Hall walk_of Hwalks.
    exact (Hpayload w Hall walk_of Hwalks).
  Qed.

  Lemma accepting_run_g5_payload_injection_from_function :
    forall word_fuel (m : @finite_nfa A)
      (Payload : Type) payloads d,
      accepting_run_g5_payload_function_on_alphabet
        word_fuel m Payload payloads d ->
      accepting_run_g5_payload_injection_on_alphabet
        word_fuel m Payload payloads d.
  Proof.
    intros word_fuel m Payload payloads d Hpayload w Hall walk_of Hwalks.
    destruct (Hpayload w Hall walk_of Hwalks) as
      [payload_of [Hinto Hinj]].
    exists payload_of. split.
    - exact Hinto.
    - intros i j Hi Hj Heq.
      injection Heq as Hred Hpayload_eq.
      eapply Hinj; eauto.
  Qed.

  Definition full_choice_endpoint_pair
      (m : @finite_nfa A)
      (w : list A)
      (i : nat)
      (q0 qf : finite_state m) : Prop :=
    exists choices start_idx tail,
      nth_error (accepting_run_full_choices m w) i = Some choices /\
      choices = start_idx :: tail /\
      nth_error (nfa_start (fnfa_base m)) start_idx = Some q0 /\
      run_choices_from (fnfa_base m) q0 w tail qf /\
      nfa_final (fnfa_base m) qf = true.

  Lemma full_choice_endpoint_pair_exists :
    forall (m : @finite_nfa A) w i,
      fnfa_well_formed m ->
      word_in_alphabet m w ->
      i < length (accepting_run_full_choices m w) ->
      exists q0 qf,
        full_choice_endpoint_pair m w i q0 qf /\
        In q0 (fnfa_states m) /\
        In qf (fnfa_states m).
  Proof.
    intros m w i Hwf Hall Hi.
    destruct
      (nth_error_exists_lt (accepting_run_full_choices m w) i Hi)
      as [choices Hchoices].
    pose proof
      (nth_error_In_lt
        (accepting_run_full_choices m w) i choices Hchoices)
      as [Hchoices_in _].
    destruct
      (accepting_run_full_choices_In_choices m w choices Hchoices_in)
      as [start_idx [q0 [tail [qf
        [Hchoices_eq [Hstart_nth [Hrun Hfinal]]]]]]].
    exists q0, qf.
    repeat split.
    - exists choices, start_idx, tail.
      repeat split; assumption.
    - destruct Hwf as [Hstarts _].
      apply Hstarts.
      eapply nth_error_In. exact Hstart_nth.
    - destruct Hwf as [Hstarts Hstep_wf].
      eapply fnfa_well_formed_path_end.
      + split; [exact Hstarts | exact Hstep_wf].
      + apply Hstarts.
        eapply nth_error_In. exact Hstart_nth.
      + exact Hall.
      + now apply run_choices_from_path with (choices := tail).
  Qed.

  Definition accepting_run_g5_endpoint_pair_separates_on_alphabet
      (word_fuel : nat)
      (m : @finite_nfa A)
      (d : nat) : Prop :=
    forall w,
      word_in_alphabet m w ->
      forall walk_of : nat -> list (quotient_component m),
        (forall i,
          i < length (accepting_run_full_choices m w) ->
          g5_red_edges_on_walk word_fuel m (walk_of i) <= d /\
          length (walk_of i) <= S (length w)) ->
        forall i j q0_i qf_i q0_j qf_j,
          i < length (accepting_run_full_choices m w) ->
          j < length (accepting_run_full_choices m w) ->
          full_choice_endpoint_pair m w i q0_i qf_i ->
          full_choice_endpoint_pair m w j q0_j qf_j ->
          g5_red_position_vector d word_fuel m (walk_of i) =
          g5_red_position_vector d word_fuel m (walk_of j) ->
          q0_i = q0_j ->
          qf_i = qf_j ->
          i = j.

  Definition optional_finite_state_pair_payloads
      (m : @finite_nfa A)
      : list (option (finite_state m * finite_state m)) :=
    None :: map Some (finite_state_pair_payloads m).

  Definition finite_state_pair_eq_dec
      (m : @finite_nfa A)
      (x y : finite_state m * finite_state m) : {x = y} + {x <> y}.
  Proof.
    decide equality; apply finite_state_eq_dec.
  Defined.

  Definition optional_finite_state_pair_eq_dec
      (m : @finite_nfa A)
      (x y : option (finite_state m * finite_state m)) : {x = y} + {x <> y}.
  Proof.
    decide equality.
    apply finite_state_pair_eq_dec.
  Defined.

  Lemma optional_finite_state_pair_payloads_NoDup :
    forall (m : @finite_nfa A),
      NoDup (optional_finite_state_pair_payloads m).
  Proof.
    intros m.
    unfold optional_finite_state_pair_payloads.
    constructor.
    - intros Hin.
      apply in_map_iff in Hin as [payload [Hnone _]].
      discriminate.
    - pose proof (finite_state_pair_payloads_NoDup m) as Hnodup.
      induction Hnodup as [| payload payloads Hnotin Hnodup IH].
      + constructor.
      + simpl. constructor.
        * intros Hin.
          apply in_map_iff in Hin as [payload' [Heq Hin]].
          inversion Heq; subst.
          contradiction.
        * exact IH.
  Qed.

  Lemma optional_finite_state_pair_payloads_length_le :
    forall (m : @finite_nfa A),
      length (optional_finite_state_pair_payloads m) <=
        S (length (fnfa_states m) * length (fnfa_states m)).
  Proof.
    intros m.
    unfold optional_finite_state_pair_payloads.
    simpl.
    rewrite map_length.
    pose proof (finite_state_pair_payloads_length_le m) as Hle.
    lia.
  Qed.

  Lemma optional_finite_state_pair_payloads_In_some :
    forall (m : @finite_nfa A) p q,
      In p (fnfa_states m) ->
      In q (fnfa_states m) ->
      In (Some (p, q)) (optional_finite_state_pair_payloads m).
  Proof.
    intros m p q Hp Hq.
    unfold optional_finite_state_pair_payloads.
    simpl. right.
    apply in_map.
    now apply finite_state_pair_payloads_In.
  Qed.

  Definition optional_state_pair_payload_index
      (m : @finite_nfa A)
      (payload : option (finite_state m * finite_state m)) : nat :=
    index_of
      (optional_finite_state_pair_eq_dec m)
      payload
      (optional_finite_state_pair_payloads m).

  Lemma optional_state_pair_payload_index_bound :
    forall (m : @finite_nfa A) payload,
      In payload (optional_finite_state_pair_payloads m) ->
      optional_state_pair_payload_index m payload <
        state_pair_payload_bound m.
  Proof.
    intros m payload Hin.
    unfold optional_state_pair_payload_index, state_pair_payload_bound.
    pose proof
      (index_of_lt
        (option (finite_state m * finite_state m))
        (optional_finite_state_pair_eq_dec m)
        payload
        (optional_finite_state_pair_payloads m)
        Hin)
      as Hidx.
    pose proof (optional_finite_state_pair_payloads_length_le m) as Hlen.
    lia.
  Qed.

  Lemma optional_state_pair_payload_index_some_bound :
    forall (m : @finite_nfa A) p q,
      In p (fnfa_states m) ->
      In q (fnfa_states m) ->
      optional_state_pair_payload_index m (Some (p, q)) <
        state_pair_payload_bound m.
  Proof.
    intros m p q Hp Hq.
    apply optional_state_pair_payload_index_bound.
    now apply optional_finite_state_pair_payloads_In_some.
  Qed.

  Definition optional_state_pair_payload_index_vector
      (m : @finite_nfa A)
      (arity : nat)
      (payloads : list (option (finite_state m * finite_state m)))
      : list nat :=
    pad_nat_vector arity
      (map (optional_state_pair_payload_index m) payloads).

  Lemma state_pair_payload_bound_positive :
    forall (m : @finite_nfa A),
      0 < state_pair_payload_bound m.
  Proof.
    intros m.
    unfold state_pair_payload_bound. lia.
  Qed.

  Lemma optional_state_pair_payload_index_vector_in :
    forall (m : @finite_nfa A) arity payloads,
      length payloads <= arity ->
      Forall
        (fun payload => In payload (optional_finite_state_pair_payloads m))
        payloads ->
      In
        (optional_state_pair_payload_index_vector m arity payloads)
        (nat_vectors_below arity (state_pair_payload_bound m)).
  Proof.
    intros m arity payloads Hlen Hall.
    unfold optional_state_pair_payload_index_vector.
    apply pad_nat_vector_in_nat_vectors_below.
    - rewrite map_length. exact Hlen.
    - apply state_pair_payload_bound_positive.
    - intros idx Hidx.
      apply in_map_iff in Hidx as [payload [Hidx Hin_payloads]].
      subst idx.
      rewrite Forall_forall in Hall.
      apply optional_state_pair_payload_index_bound.
      now apply Hall.
  Qed.

  Definition optional_state_pair_payload_positive_index
      (m : @finite_nfa A)
      (payload : option (finite_state m * finite_state m)) : nat :=
    S (optional_state_pair_payload_index m payload).

  Definition optional_state_pair_payload_positive_index_vector
      (m : @finite_nfa A)
      (arity : nat)
      (payloads : list (option (finite_state m * finite_state m)))
      : list nat :=
    pad_positive_nat_vector arity
      (map (optional_state_pair_payload_positive_index m) payloads).

  Lemma optional_state_pair_payload_positive_index_pos :
    forall (m : @finite_nfa A) payload,
      0 < optional_state_pair_payload_positive_index m payload.
  Proof.
    intros m payload.
    unfold optional_state_pair_payload_positive_index. lia.
  Qed.

  Lemma optional_state_pair_payload_positive_index_bound :
    forall (m : @finite_nfa A) payload,
      In payload (optional_finite_state_pair_payloads m) ->
      optional_state_pair_payload_positive_index m payload <
        S (state_pair_payload_bound m).
  Proof.
    intros m payload Hin.
    unfold optional_state_pair_payload_positive_index.
    pose proof (optional_state_pair_payload_index_bound m payload Hin).
    lia.
  Qed.

  Lemma optional_state_pair_payload_positive_index_injective :
    forall (m : @finite_nfa A) p q,
      In p (optional_finite_state_pair_payloads m) ->
      In q (optional_finite_state_pair_payloads m) ->
      optional_state_pair_payload_positive_index m p =
      optional_state_pair_payload_positive_index m q ->
      p = q.
  Proof.
    intros m p q Hp Hq Heq.
    unfold optional_state_pair_payload_positive_index in Heq.
    injection Heq as Hidx.
    unfold optional_state_pair_payload_index in Hidx.
    eapply index_of_NoDup_eq; eauto.
    apply optional_finite_state_pair_payloads_NoDup.
  Qed.

  Lemma optional_state_pair_payload_positive_indices_eq :
    forall (m : @finite_nfa A) xs ys,
      Forall
        (fun payload => In payload (optional_finite_state_pair_payloads m))
        xs ->
      Forall
        (fun payload => In payload (optional_finite_state_pair_payloads m))
        ys ->
      map (optional_state_pair_payload_positive_index m) xs =
      map (optional_state_pair_payload_positive_index m) ys ->
      xs = ys.
  Proof.
    intros m xs.
    induction xs as [| x xs IH]; intros ys Hall_x Hall_y Heq;
      destruct ys as [| y ys]; simpl in Heq; try discriminate; auto.
    inversion Hall_x as [| ? ? Hx Hxs]; subst.
    inversion Hall_y as [| ? ? Hy Hys]; subst.
    injection Heq as Hxy Htail.
    f_equal.
    - unfold optional_state_pair_payload_index in Hxy.
      eapply index_of_NoDup_eq.
      + apply optional_finite_state_pair_payloads_NoDup.
      + exact Hx.
      + exact Hy.
      + exact Hxy.
    - eapply IH.
      + exact Hxs.
      + exact Hys.
      + exact Htail.
  Qed.

  Lemma optional_state_pair_payload_positive_index_vector_in :
    forall (m : @finite_nfa A) arity payloads,
      length payloads <= arity ->
      Forall
        (fun payload => In payload (optional_finite_state_pair_payloads m))
        payloads ->
      In
        (optional_state_pair_payload_positive_index_vector m arity payloads)
        (nat_vectors_below arity (S (state_pair_payload_bound m))).
  Proof.
    intros m arity payloads Hlen Hall.
    unfold optional_state_pair_payload_positive_index_vector.
    apply pad_positive_nat_vector_in_nat_vectors_below.
    - rewrite map_length. exact Hlen.
    - lia.
    - intros idx Hidx.
      apply in_map_iff in Hidx as [payload [Hidx Hin_payloads]].
      subst idx.
      rewrite Forall_forall in Hall.
      apply optional_state_pair_payload_positive_index_bound.
      now apply Hall.
  Qed.

  Lemma optional_state_pair_payload_positive_index_vector_eq :
    forall (m : @finite_nfa A) arity xs ys,
      length xs <= arity ->
      length ys <= arity ->
      Forall
        (fun payload => In payload (optional_finite_state_pair_payloads m))
        xs ->
      Forall
        (fun payload => In payload (optional_finite_state_pair_payloads m))
        ys ->
      optional_state_pair_payload_positive_index_vector m arity xs =
      optional_state_pair_payload_positive_index_vector m arity ys ->
      xs = ys.
  Proof.
    intros m arity xs ys Hlen_x Hlen_y Hall_x Hall_y Heq.
    unfold optional_state_pair_payload_positive_index_vector in Heq.
    eapply optional_state_pair_payload_positive_indices_eq.
    - exact Hall_x.
    - exact Hall_y.
    - eapply pad_positive_nat_vector_eq.
      + rewrite map_length. exact Hlen_x.
      + rewrite map_length. exact Hlen_y.
      + intros idx Hidx.
        apply in_map_iff in Hidx as [payload [Hidx _]].
        subst idx.
        apply optional_state_pair_payload_positive_index_pos.
      + intros idx Hidx.
        apply in_map_iff in Hidx as [payload [Hidx _]].
        subst idx.
        apply optional_state_pair_payload_positive_index_pos.
      + exact Heq.
  Qed.

  Definition accepting_run_g5_boundary_pair_payload_function_on_alphabet
      (word_fuel : nat)
      (m : @finite_nfa A)
      (d : nat) : Prop :=
    forall w,
      word_in_alphabet m w ->
      forall walk_of : nat -> list (quotient_component m),
        (forall i,
          i < length (accepting_run_full_choices m w) ->
          g5_red_edges_on_walk word_fuel m (walk_of i) <= d /\
          length (walk_of i) <= S (length w)) ->
        exists payloads_of :
          nat -> list (option (finite_state m * finite_state m)),
          (forall i,
            i < length (accepting_run_full_choices m w) ->
            length (payloads_of i) <= S d /\
            Forall
              (fun payload =>
                In payload (optional_finite_state_pair_payloads m))
              (payloads_of i)) /\
          (forall i j,
            i < length (accepting_run_full_choices m w) ->
            j < length (accepting_run_full_choices m w) ->
            g5_red_position_vector d word_fuel m (walk_of i) =
            g5_red_position_vector d word_fuel m (walk_of j) ->
            optional_state_pair_payload_index_vector
              m (S d) (payloads_of i) =
            optional_state_pair_payload_index_vector
              m (S d) (payloads_of j) ->
            i = j).

  Lemma accepting_run_g5_boundary_indices_from_pair_payloads :
    forall word_fuel (m : @finite_nfa A) d,
      accepting_run_g5_boundary_pair_payload_function_on_alphabet
        word_fuel m d ->
      accepting_run_g5_boundary_index_payload_function_on_alphabet
        word_fuel m d.
  Proof.
    intros word_fuel m d Hpayload w Hall walk_of Hwalks.
    destruct (Hpayload w Hall walk_of Hwalks)
      as [payloads_of [Hvalid Hinj]].
    exists
      (fun i =>
        optional_state_pair_payload_index_vector m (S d) (payloads_of i)).
    split.
    - intros i Hi.
      destruct (Hvalid i Hi) as [Hlen Hall_payloads].
      now apply optional_state_pair_payload_index_vector_in.
    - intros i j Hi Hj Hred Hpayload_eq.
      eapply Hinj; eauto.
  Qed.

  Fixpoint trace_state_pair_at
      (m : @finite_nfa A)
      (trace : list (finite_state m))
      (pos : nat) : option (finite_state m * finite_state m) :=
    match pos, trace with
    | O, p :: q :: _ => Some (p, q)
    | S pos', _ :: trace' => trace_state_pair_at m trace' pos'
    | _, _ => None
    end.

  Lemma trace_state_pair_at_nth :
    forall (m : @finite_nfa A) trace pos p q,
      trace_state_pair_at m trace pos = Some (p, q) ->
      nth_error trace pos = Some p /\
      nth_error trace (S pos) = Some q.
  Proof.
    intros m trace pos.
    revert trace.
    induction pos as [| pos IH]; intros trace p q Hpair;
      destruct trace as [| x trace']; simpl in *; try discriminate.
    - destruct trace' as [| y trace'']; simpl in *; try discriminate.
      inversion Hpair; subst. auto.
    - apply IH in Hpair.
      destruct Hpair as [Hp Hq].
      auto.
  Qed.

  Lemma trace_state_pair_at_useful_from_accepting_trace :
    forall (m : @finite_nfa A) q0 w qf trace pos p q,
      In q0 (nfa_start (fnfa_base m)) ->
      run_trace_from (fnfa_base m) q0 w qf trace ->
      nfa_final (fnfa_base m) qf = true ->
      trace_state_pair_at m trace pos = Some (p, q) ->
      finite_useful m p /\ finite_useful m q.
  Proof.
    intros m q0 w qf trace pos p q Hstart Htrace Hfinal Hpair.
    destruct (trace_state_pair_at_nth m trace pos p q Hpair)
      as [Hp Hq].
    split;
      eapply finite_useful_from_accepting_trace_nth; eauto.
  Qed.

  Lemma accepting_run_full_choice_trace_pair_step_split :
    forall (m : @finite_nfa A) w i choices start_idx tail q0 qf
      trace pos p r a,
      nth_error (accepting_run_full_choices m w) i = Some choices ->
      choices = start_idx :: tail ->
      nth_error (nfa_start (fnfa_base m)) start_idx = Some q0 ->
      run_choices_from (fnfa_base m) q0 w tail qf ->
      nfa_final (fnfa_base m) qf = true ->
      replay_choices_from (fnfa_base m) q0 w tail = Some trace ->
      trace_state_pair_at m trace pos = Some (p, r) ->
      nth_error w pos = Some a ->
      exists u v cu idx cv,
        w = u ++ a :: v /\
        tail = cu ++ idx :: cv /\
        length u = pos /\
        run_choices_from (fnfa_base m) q0 u cu p /\
        nth_error (nfa_step (fnfa_base m) p a) idx = Some r /\
        run_choices_from (fnfa_base m) r v cv qf /\
        finite_useful m p /\
        finite_useful m r.
  Proof.
    intros m w i choices start_idx tail q0 qf trace pos p r a
      Hchoices Hchoices_eq Hstart Hrun Hfinal Hreplay Hpair Hword.
    destruct (trace_state_pair_at_nth m trace pos p r Hpair)
      as [Htrace_p Htrace_r].
    destruct
      (replay_choices_from_step_split
        (fnfa_base m) q0 w tail qf trace pos a p r
        Hrun Hreplay Htrace_p Htrace_r Hword)
      as [u [v [cu [idx [cv Hsplit]]]]].
    destruct Hsplit as
      [Hw [Htail_eq [Hlen [Hleft [Hstep Hright]]]]].
    assert (Hstart_in : In q0 (nfa_start (fnfa_base m))).
    {
      eapply nth_error_In. exact Hstart.
    }
    assert (Htrace : run_trace_from (fnfa_base m) q0 w qf trace).
    {
      destruct
        (replay_choices_from_run_choices
          (fnfa_base m) q0 w tail qf Hrun)
        as [trace0 [Hreplay0 Htrace0]].
      rewrite Hreplay in Hreplay0.
      inversion Hreplay0; subst trace0.
      exact Htrace0.
    }
    destruct
      (trace_state_pair_at_useful_from_accepting_trace
        m q0 w qf trace pos p r Hstart_in Htrace Hfinal Hpair)
      as [Hp_useful Hr_useful].
    exists u, v, cu, idx, cv.
    repeat split; assumption.
  Qed.

  Definition trace_red_boundary_payloads
      (word_fuel : nat)
      (m : @finite_nfa A)
      (walk : list (quotient_component m))
      (trace : list (finite_state m))
      : list (option (finite_state m * finite_state m)) :=
    map
      (trace_state_pair_at m trace)
      (g5_red_positions_on_walk word_fuel m walk).

  Lemma optional_finite_state_pair_payloads_In_none :
    forall (m : @finite_nfa A),
      In None (optional_finite_state_pair_payloads m).
  Proof.
    intros m. unfold optional_finite_state_pair_payloads. simpl. auto.
  Qed.

  Lemma trace_state_pair_at_payload_in :
    forall (m : @finite_nfa A) trace pos,
      Forall (fun q => In q (fnfa_states m)) trace ->
      In
        (trace_state_pair_at m trace pos)
        (optional_finite_state_pair_payloads m).
  Proof.
    intros m trace pos Hall.
    revert trace Hall.
    induction pos as [| pos IH]; intros trace Hall;
      destruct trace as [| p trace']; simpl.
    - apply optional_finite_state_pair_payloads_In_none.
    - destruct trace' as [| q trace''].
      + apply optional_finite_state_pair_payloads_In_none.
      + inversion Hall as [| ? ? Hp Htail]; subst.
        inversion Htail as [| ? ? Hq _]; subst.
        apply optional_finite_state_pair_payloads_In_some; assumption.
    - apply optional_finite_state_pair_payloads_In_none.
    - inversion Hall as [| ? ? _ Htail]; subst.
      now apply IH.
  Qed.

  Lemma trace_red_boundary_payloads_length :
    forall word_fuel (m : @finite_nfa A) walk trace,
      length (trace_red_boundary_payloads word_fuel m walk trace) =
      g5_red_edges_on_walk word_fuel m walk.
  Proof.
    intros word_fuel m walk trace.
    unfold trace_red_boundary_payloads.
    rewrite map_length.
    apply g5_red_positions_on_walk_length.
  Qed.

  Lemma trace_red_boundary_payloads_valid :
    forall word_fuel (m : @finite_nfa A) walk trace d,
      Forall (fun q => In q (fnfa_states m)) trace ->
      g5_red_edges_on_walk word_fuel m walk <= d ->
      length (trace_red_boundary_payloads word_fuel m walk trace) <= S d /\
      Forall
        (fun payload => In payload (optional_finite_state_pair_payloads m))
        (trace_red_boundary_payloads word_fuel m walk trace).
  Proof.
    intros word_fuel m walk trace d Htrace Hred.
    split.
    - rewrite trace_red_boundary_payloads_length. lia.
    - unfold trace_red_boundary_payloads.
      apply Forall_forall.
      intros payload Hpayload.
      apply in_map_iff in Hpayload as [pos [Hpayload Hpos]].
      subst payload.
      now apply trace_state_pair_at_payload_in.
  Qed.

  Lemma trace_red_boundary_payloads_positive_vector_eq :
    forall word_fuel (m : @finite_nfa A) d walk1 trace1 walk2 trace2,
      Forall (fun q => In q (fnfa_states m)) trace1 ->
      Forall (fun q => In q (fnfa_states m)) trace2 ->
      g5_red_edges_on_walk word_fuel m walk1 <= d ->
      g5_red_edges_on_walk word_fuel m walk2 <= d ->
      optional_state_pair_payload_positive_index_vector
        m (S d)
        (trace_red_boundary_payloads word_fuel m walk1 trace1) =
      optional_state_pair_payload_positive_index_vector
        m (S d)
        (trace_red_boundary_payloads word_fuel m walk2 trace2) ->
      trace_red_boundary_payloads word_fuel m walk1 trace1 =
      trace_red_boundary_payloads word_fuel m walk2 trace2.
  Proof.
    intros word_fuel m d walk1 trace1 walk2 trace2
      Htrace1 Htrace2 Hred1 Hred2 Hvec.
    destruct
      (trace_red_boundary_payloads_valid
        word_fuel m walk1 trace1 d Htrace1 Hred1)
      as [Hlen1 Hall1].
    destruct
      (trace_red_boundary_payloads_valid
        word_fuel m walk2 trace2 d Htrace2 Hred2)
      as [Hlen2 Hall2].
    eapply optional_state_pair_payload_positive_index_vector_eq; eauto.
  Qed.

  Definition accepting_run_g5_trace_boundary_payloads_separate_on_alphabet
      (word_fuel : nat)
      (m : @finite_nfa A)
      (d : nat) : Prop :=
    forall w,
      word_in_alphabet m w ->
      forall
        (walk_of : nat -> list (quotient_component m))
        (trace_of : nat -> list (finite_state m)),
        (forall i,
          i < length (accepting_run_full_choices m w) ->
          g5_red_edges_on_walk word_fuel m (walk_of i) <= d /\
          length (walk_of i) <= S (length w) /\
          Forall (fun q => In q (fnfa_states m)) (trace_of i)) ->
        forall i j,
          i < length (accepting_run_full_choices m w) ->
          j < length (accepting_run_full_choices m w) ->
          g5_red_position_vector d word_fuel m (walk_of i) =
          g5_red_position_vector d word_fuel m (walk_of j) ->
          optional_state_pair_payload_index_vector
            m (S d)
            (trace_red_boundary_payloads word_fuel m (walk_of i) (trace_of i)) =
          optional_state_pair_payload_index_vector
            m (S d)
            (trace_red_boundary_payloads word_fuel m (walk_of j) (trace_of j)) ->
          i = j.

  Definition accepting_run_g5_trace_boundary_positive_payloads_separate_on_alphabet
      (word_fuel : nat)
      (m : @finite_nfa A)
      (d : nat) : Prop :=
    forall w,
      word_in_alphabet m w ->
      forall
        (walk_of : nat -> list (quotient_component m))
        (trace_of : nat -> list (finite_state m)),
        (forall i,
          i < length (accepting_run_full_choices m w) ->
          g5_red_edges_on_walk word_fuel m (walk_of i) <= d /\
          length (walk_of i) <= S (length w) /\
          Forall (fun q => In q (fnfa_states m)) (trace_of i)) ->
        forall i j,
          i < length (accepting_run_full_choices m w) ->
          j < length (accepting_run_full_choices m w) ->
          g5_red_position_vector d word_fuel m (walk_of i) =
          g5_red_position_vector d word_fuel m (walk_of j) ->
          optional_state_pair_payload_positive_index_vector
            m (S d)
            (trace_red_boundary_payloads word_fuel m (walk_of i) (trace_of i)) =
          optional_state_pair_payload_positive_index_vector
            m (S d)
            (trace_red_boundary_payloads word_fuel m (walk_of j) (trace_of j)) ->
          i = j.

  Definition trace_boundary_payload_collision
      (word_fuel : nat)
      (m : @finite_nfa A)
      (d : nat)
      (w : list A)
      (walk_of : nat -> list (quotient_component m))
      (trace_of : nat -> list (finite_state m)) : Prop :=
    exists i j,
      i < length (accepting_run_full_choices m w) /\
      j < length (accepting_run_full_choices m w) /\
      i <> j /\
      g5_red_position_vector d word_fuel m (walk_of i) =
      g5_red_position_vector d word_fuel m (walk_of j) /\
      optional_state_pair_payload_index_vector
        m (S d)
        (trace_red_boundary_payloads word_fuel m (walk_of i) (trace_of i)) =
      optional_state_pair_payload_index_vector
        m (S d)
        (trace_red_boundary_payloads word_fuel m (walk_of j) (trace_of j)).

  Definition trace_boundary_positive_payload_collision
      (word_fuel : nat)
      (m : @finite_nfa A)
      (d : nat)
      (w : list A)
      (walk_of : nat -> list (quotient_component m))
      (trace_of : nat -> list (finite_state m)) : Prop :=
    exists i j,
      i < length (accepting_run_full_choices m w) /\
      j < length (accepting_run_full_choices m w) /\
      i <> j /\
      g5_red_position_vector d word_fuel m (walk_of i) =
      g5_red_position_vector d word_fuel m (walk_of j) /\
      optional_state_pair_payload_positive_index_vector
        m (S d)
        (trace_red_boundary_payloads word_fuel m (walk_of i) (trace_of i)) =
      optional_state_pair_payload_positive_index_vector
        m (S d)
        (trace_red_boundary_payloads word_fuel m (walk_of j) (trace_of j)).

  Definition trace_boundary_payload_list_collision
      (word_fuel : nat)
      (m : @finite_nfa A)
      (d : nat)
      (w : list A)
      (walk_of : nat -> list (quotient_component m))
      (trace_of : nat -> list (finite_state m)) : Prop :=
    exists i j,
      i < length (accepting_run_full_choices m w) /\
      j < length (accepting_run_full_choices m w) /\
      i <> j /\
      g5_red_position_vector d word_fuel m (walk_of i) =
      g5_red_position_vector d word_fuel m (walk_of j) /\
      trace_red_boundary_payloads word_fuel m (walk_of i) (trace_of i) =
      trace_red_boundary_payloads word_fuel m (walk_of j) (trace_of j).

  Definition trace_boundary_payload_collisions_imply_EDA_on_alphabet
      (word_fuel : nat)
      (m : @finite_nfa A)
      (d : nat) : Prop :=
    forall w,
      word_in_alphabet m w ->
      forall
        (walk_of : nat -> list (quotient_component m))
        (trace_of : nat -> list (finite_state m)),
        (forall i,
          i < length (accepting_run_full_choices m w) ->
          g5_red_edges_on_walk word_fuel m (walk_of i) <= d /\
          length (walk_of i) <= S (length w) /\
          Forall (fun q => In q (fnfa_states m)) (trace_of i)) ->
        trace_boundary_payload_collision word_fuel m d w walk_of trace_of ->
        EDA m.

  Definition trace_boundary_positive_payload_collisions_imply_EDA_on_alphabet
      (word_fuel : nat)
      (m : @finite_nfa A)
      (d : nat) : Prop :=
    forall w,
      word_in_alphabet m w ->
      forall
        (walk_of : nat -> list (quotient_component m))
        (trace_of : nat -> list (finite_state m)),
        (forall i,
          i < length (accepting_run_full_choices m w) ->
          g5_red_edges_on_walk word_fuel m (walk_of i) <= d /\
          length (walk_of i) <= S (length w) /\
          Forall (fun q => In q (fnfa_states m)) (trace_of i)) ->
        trace_boundary_positive_payload_collision
          word_fuel m d w walk_of trace_of ->
        EDA m.

  Definition trace_boundary_payload_list_collisions_imply_EDA_on_alphabet
      (word_fuel : nat)
      (m : @finite_nfa A)
      (d : nat) : Prop :=
    forall w,
      word_in_alphabet m w ->
      forall
        (walk_of : nat -> list (quotient_component m))
        (trace_of : nat -> list (finite_state m)),
        (forall i,
          i < length (accepting_run_full_choices m w) ->
          g5_red_edges_on_walk word_fuel m (walk_of i) <= d /\
          length (walk_of i) <= S (length w) /\
          Forall (fun q => In q (fnfa_states m)) (trace_of i)) ->
        trace_boundary_payload_list_collision word_fuel m d w walk_of trace_of ->
        EDA m.

  Lemma trace_boundary_positive_collision_to_list_collision :
    forall word_fuel (m : @finite_nfa A) d w walk_of trace_of,
      (forall i,
        i < length (accepting_run_full_choices m w) ->
        g5_red_edges_on_walk word_fuel m (walk_of i) <= d /\
        length (walk_of i) <= S (length w) /\
        Forall (fun q => In q (fnfa_states m)) (trace_of i)) ->
      trace_boundary_positive_payload_collision
        word_fuel m d w walk_of trace_of ->
      trace_boundary_payload_list_collision
        word_fuel m d w walk_of trace_of.
  Proof.
    intros word_fuel m d w walk_of trace_of Hvalid Hcollision.
    destruct Hcollision as
      [i [j [Hi [Hj [Hneq [Hred Hpayload]]]]]].
    destruct (Hvalid i Hi) as [Hred_i [_Hlen_i Htrace_i]].
    destruct (Hvalid j Hj) as [Hred_j [_Hlen_j Htrace_j]].
    exists i, j.
    repeat split; try assumption.
    eapply trace_red_boundary_payloads_positive_vector_eq; eauto.
  Qed.

  Lemma trace_boundary_positive_collisions_imply_EDA_from_list_collisions :
    forall word_fuel (m : @finite_nfa A) d,
      trace_boundary_payload_list_collisions_imply_EDA_on_alphabet
        word_fuel m d ->
      trace_boundary_positive_payload_collisions_imply_EDA_on_alphabet
        word_fuel m d.
  Proof.
    intros word_fuel m d Hlist w Hall walk_of trace_of Hvalid Hcollision.
    eapply Hlist; eauto.
    now apply trace_boundary_positive_collision_to_list_collision.
  Qed.

  Lemma trace_boundary_payload_separator_from_no_EDA :
    forall word_fuel (m : @finite_nfa A) d,
      no_EDA m ->
      trace_boundary_payload_collisions_imply_EDA_on_alphabet
        word_fuel m d ->
      accepting_run_g5_trace_boundary_payloads_separate_on_alphabet
        word_fuel m d.
  Proof.
    intros word_fuel m d Hno Hcollision_to_eda
      w Hall walk_of trace_of Hvalid i j Hi Hj Hred Hpayload.
    destruct (Nat.eq_dec i j) as [Heq | Hneq]; [exact Heq |].
    exfalso.
    apply Hno.
    eapply Hcollision_to_eda; eauto.
    exists i, j.
    repeat split; assumption.
  Qed.

  Lemma trace_boundary_positive_payload_separator_from_no_EDA :
    forall word_fuel (m : @finite_nfa A) d,
      no_EDA m ->
      trace_boundary_positive_payload_collisions_imply_EDA_on_alphabet
        word_fuel m d ->
      accepting_run_g5_trace_boundary_positive_payloads_separate_on_alphabet
        word_fuel m d.
  Proof.
    intros word_fuel m d Hno Hcollision_to_eda
      w Hall walk_of trace_of Hvalid i j Hi Hj Hred Hpayload.
    destruct (Nat.eq_dec i j) as [Heq | Hneq]; [exact Heq |].
    exfalso.
    apply Hno.
    eapply Hcollision_to_eda; eauto.
    exists i, j.
    repeat split; assumption.
  Qed.

  Lemma accepting_run_g5_boundary_pairs_from_trace_separator :
    forall word_fuel (m : @finite_nfa A) d,
      fnfa_well_formed m ->
      accepting_run_g5_trace_boundary_payloads_separate_on_alphabet
        word_fuel m d ->
      accepting_run_g5_boundary_pair_payload_function_on_alphabet
        word_fuel m d.
  Proof.
    intros word_fuel m d Hwf Hsep w Hall walk_of Hwalks.
    set (n := length (accepting_run_full_choices m w)).
    destruct
      (finite_index_choice_list
        (list (finite_state m))
        n
        (fun i trace =>
          exists choices start_idx tail q0 qf,
            nth_error (accepting_run_full_choices m w) i = Some choices /\
            choices = start_idx :: tail /\
            nth_error (nfa_start (fnfa_base m)) start_idx = Some q0 /\
            run_choices_from (fnfa_base m) q0 w tail qf /\
            nfa_final (fnfa_base m) qf = true /\
            replay_choices_from (fnfa_base m) q0 w tail = Some trace /\
            run_trace_from (fnfa_base m) q0 w qf trace /\
            Forall (fun q => In q (fnfa_states m)) trace))
      as [traces_for_run [Htraces_len Htraces_for_run]].
    {
      intros i Hi.
      subst n.
      destruct (accepting_run_full_choice_replay_trace m w i Hi)
        as (choices & start_idx & tail & q0 & qf & trace &
          Hchoices & Hchoices_eq & Hstart_nth & Hrun & Hfinal &
          Hreplay & Htrace & _).
      assert (Hq0_states : In q0 (fnfa_states m)).
      {
        destruct Hwf as [Hstarts _].
        apply Hstarts.
        eapply nth_error_In. exact Hstart_nth.
      }
      assert (Htrace_states :
        Forall (fun q => In q (fnfa_states m)) trace).
      {
        eapply run_trace_from_states; eauto.
      }
      exists trace.
      exists choices, start_idx, tail, q0, qf.
      repeat split; assumption.
    }
    set (trace_of := fun i =>
      match nth_error traces_for_run i with
      | Some trace => trace
      | None => []
      end).
    exists
      (fun i => trace_red_boundary_payloads word_fuel m (walk_of i) (trace_of i)).
    split.
    - intros i Hi.
      subst n.
      destruct (Htraces_for_run i Hi) as
        (trace & Hnth & choices & start_idx & tail & q0 & qf &
          Hchoices & Hchoices_eq & Hstart_nth & Hrun & Hfinal &
          Hreplay & Htrace & Htrace_states).
      unfold trace_of.
      rewrite Hnth.
      destruct (Hwalks i Hi) as [Hred Hlen].
      now apply trace_red_boundary_payloads_valid.
    - intros i j Hi Hj Hred Hpayload.
      subst n.
      eapply Hsep with (trace_of := trace_of); eauto.
      intros k Hk.
      destruct (Htraces_for_run k Hk) as
        (trace & Hnth & choices & start_idx & tail & q0 & qf &
          Hchoices & Hchoices_eq & Hstart_nth & Hrun & Hfinal &
          Hreplay & Htrace & Htrace_states).
      unfold trace_of.
      rewrite Hnth.
      destruct (Hwalks k Hk) as [Hred_k Hlen_k].
      repeat split; assumption.
  Qed.

  Lemma accepting_run_g5_positive_boundary_indices_from_trace_separator :
    forall word_fuel (m : @finite_nfa A) d,
      fnfa_well_formed m ->
      accepting_run_g5_trace_boundary_positive_payloads_separate_on_alphabet
        word_fuel m d ->
      accepting_run_g5_positive_boundary_index_payload_function_on_alphabet
        word_fuel m d.
  Proof.
    intros word_fuel m d Hwf Hsep w Hall walk_of Hwalks.
    set (n := length (accepting_run_full_choices m w)).
    destruct
      (finite_index_choice_list
        (list (finite_state m))
        n
        (fun i trace =>
          exists choices start_idx tail q0 qf,
            nth_error (accepting_run_full_choices m w) i = Some choices /\
            choices = start_idx :: tail /\
            nth_error (nfa_start (fnfa_base m)) start_idx = Some q0 /\
            run_choices_from (fnfa_base m) q0 w tail qf /\
            nfa_final (fnfa_base m) qf = true /\
            replay_choices_from (fnfa_base m) q0 w tail = Some trace /\
            run_trace_from (fnfa_base m) q0 w qf trace /\
            Forall (fun q => In q (fnfa_states m)) trace))
      as [traces_for_run [Htraces_len Htraces_for_run]].
    {
      intros i Hi.
      subst n.
      destruct (accepting_run_full_choice_replay_trace m w i Hi)
        as (choices & start_idx & tail & q0 & qf & trace &
          Hchoices & Hchoices_eq & Hstart_nth & Hrun & Hfinal &
          Hreplay & Htrace & _).
      assert (Hq0_states : In q0 (fnfa_states m)).
      {
        destruct Hwf as [Hstarts _].
        apply Hstarts.
        eapply nth_error_In. exact Hstart_nth.
      }
      assert (Htrace_states :
        Forall (fun q => In q (fnfa_states m)) trace).
      {
        eapply run_trace_from_states; eauto.
      }
      exists trace.
      exists choices, start_idx, tail, q0, qf.
      repeat split; assumption.
    }
    set (trace_of := fun i =>
      match nth_error traces_for_run i with
      | Some trace => trace
      | None => []
      end).
    exists
      (fun i =>
        optional_state_pair_payload_positive_index_vector
          m (S d)
          (trace_red_boundary_payloads word_fuel m (walk_of i) (trace_of i))).
    split.
    - intros i Hi.
      subst n.
      destruct (Htraces_for_run i Hi) as
        (trace & Hnth & choices & start_idx & tail & q0 & qf &
          Hchoices & Hchoices_eq & Hstart_nth & Hrun & Hfinal &
          Hreplay & Htrace & Htrace_states).
      unfold trace_of.
      rewrite Hnth.
      destruct (Hwalks i Hi) as [Hred Hlen].
      destruct
        (trace_red_boundary_payloads_valid
          word_fuel m (walk_of i) trace d Htrace_states Hred)
        as [Hpayload_len Hpayload_all].
      now apply optional_state_pair_payload_positive_index_vector_in.
    - intros i j Hi Hj Hred Hpayload.
      subst n.
      eapply Hsep with (trace_of := trace_of); eauto.
      intros k Hk.
      destruct (Htraces_for_run k Hk) as
        (trace & Hnth & choices & start_idx & tail & q0 & qf &
          Hchoices & Hchoices_eq & Hstart_nth & Hrun & Hfinal &
          Hreplay & Htrace & Htrace_states).
      unfold trace_of.
      rewrite Hnth.
      destruct (Hwalks k Hk) as [Hred_k Hlen_k].
      repeat split; assumption.
  Qed.

  Lemma accepting_run_g5_payload_function_from_endpoint_pairs :
    forall word_fuel (m : @finite_nfa A) d,
      fnfa_well_formed m ->
      accepting_run_g5_endpoint_pair_separates_on_alphabet
        word_fuel m d ->
      accepting_run_g5_payload_function_on_alphabet
        word_fuel m
        (option (finite_state m * finite_state m))
        (optional_finite_state_pair_payloads m)
        d.
  Proof.
    intros word_fuel m d Hwf Hseparate w Hall walk_of Hwalks.
    set (n := length (accepting_run_full_choices m w)).
    destruct
      (finite_index_choice_list
        (option (finite_state m * finite_state m))
        n
        (fun i payload =>
          exists q0 qf,
            payload = Some (q0, qf) /\
            full_choice_endpoint_pair m w i q0 qf /\
            In payload (optional_finite_state_pair_payloads m)))
      as [payloads_for_run [Hpayloads_len Hpayloads_for_run]].
    {
      intros i Hi.
      subst n.
      destruct
        (full_choice_endpoint_pair_exists m w i Hwf Hall Hi)
        as [q0 [qf [Hpair [Hq0 Hqf]]]].
      exists (Some (q0, qf)).
      exists q0, qf.
      repeat split; auto.
      now apply optional_finite_state_pair_payloads_In_some.
    }
    exists
      (fun i =>
        match nth_error payloads_for_run i with
        | Some payload => payload
        | None => None
        end).
    split.
    - intros i Hi.
      subst n.
      destruct (Hpayloads_for_run i Hi) as
        [payload [Hnth [q0 [qf [Hpayload [_ Hin]]]]]].
      rewrite Hnth. exact Hin.
    - intros i j Hi Hj Hred Hpayload_eq.
      subst n.
      destruct (Hpayloads_for_run i Hi) as
        [payload_i [Hnth_i [q0_i [qf_i
          [Hpayload_i [Hpair_i _]]]]]].
      destruct (Hpayloads_for_run j Hj) as
        [payload_j [Hnth_j [q0_j [qf_j
          [Hpayload_j [Hpair_j _]]]]]].
      rewrite Hnth_i in Hpayload_eq.
      rewrite Hnth_j in Hpayload_eq.
      rewrite Hpayload_i in Hpayload_eq.
      rewrite Hpayload_j in Hpayload_eq.
      injection Hpayload_eq as Hq0_eq Hqf_eq.
      eapply Hseparate; eauto.
  Qed.

  Lemma accepting_run_g5_walk_signatures_from_witnesses_and_payloads :
    forall word_fuel (m : @finite_nfa A) (Payload : Type) payloads d c,
      NoDup payloads ->
      length payloads <= c ->
      accepting_run_g5_walk_witnesses_on_alphabet word_fuel m d ->
      accepting_run_g5_payload_injection_on_alphabet
        word_fuel m Payload payloads d ->
      accepting_run_g5_walk_signatures_on_alphabet
        word_fuel m Payload payloads d c.
  Proof.
    intros word_fuel m Payload payloads d c
      Hnodup Hpayload_bound Hwalks Hpayloads.
    repeat split; auto.
    intros w Hall.
    destruct (Hwalks w Hall) as [walk_of Hwalk_of].
    destruct (Hpayloads w Hall walk_of Hwalk_of) as
      [payload_of [Hpayload_of Hinj]].
    exists walk_of, payload_of.
    split.
    - intros i Hi.
      destruct (Hwalk_of i Hi) as [Hred Hlen].
      repeat split; auto.
    - exact Hinj.
  Qed.

  Theorem degree_at_most_on_alphabet_from_run_g5_witnesses_and_payloads :
    forall word_fuel (m : @finite_nfa A) (Payload : Type) payloads d c,
      NoDup payloads ->
      length payloads <= c ->
      accepting_run_g5_walk_witnesses_on_alphabet word_fuel m d ->
      accepting_run_g5_payload_injection_on_alphabet
        word_fuel m Payload payloads d ->
      degree_at_most_on_alphabet m d.
  Proof.
    intros word_fuel m Payload payloads d c
      Hnodup Hpayload_bound Hwalks Hpayloads.
    eapply degree_at_most_on_alphabet_from_run_g5_walk_signatures.
    eapply accepting_run_g5_walk_signatures_from_witnesses_and_payloads;
      eauto.
  Qed.

  Definition accepting_run_g5_walk_witnesses_on_bounded_words
      (word_fuel graph_fuel : nat)
      (m : @finite_nfa A)
      (d : nat) : Prop :=
    let components := scc_quotient_with_fuel graph_fuel m in
    forall w,
      word_in_alphabet m w ->
      length w <= length components ->
      exists walk_of : nat -> list (quotient_component m),
        forall i,
          i < length (accepting_run_full_choices m w) ->
          g5_red_edges_on_walk word_fuel m (walk_of i) <= d /\
          length (walk_of i) <= S (length w).

  Lemma accepting_run_g5_walk_witnesses_on_bounded_words_from_max :
    forall word_fuel graph_fuel (m : @finite_nfa A) k,
      full_choice_g5_witness_bound word_fuel graph_fuel m k ->
      accepting_run_g5_walk_witnesses_on_bounded_words
        word_fuel graph_fuel m k.
  Proof.
    intros word_fuel graph_fuel m k Hbound w Hall Hlen_word.
    set (n := length (accepting_run_full_choices m w)).
    destruct
      (finite_index_choice_list
        (list (quotient_component m))
        n
        (fun i walk =>
          g5_walkb word_fuel graph_fuel m walk = true /\
          g5_red_edges_on_walk word_fuel m walk <= k /\
          length walk <= S (length w)))
      as [walks [Hwalks_len Hwalks]].
    {
      intros i Hi.
      subst n.
      eapply full_choice_g5_witnesses_from_max; eauto.
    }
    exists
      (fun i =>
        match nth_error walks i with
        | Some walk => walk
        | None => []
        end).
    intros i Hi.
    subst n.
    destruct (Hwalks i Hi) as [walk [Hnth [_ [Hred Hlen]]]].
    rewrite Hnth. auto.
  Qed.

  Lemma accepting_run_g5_walk_witnesses_on_bounded_words_from_max_le :
    forall word_fuel graph_fuel (m : @finite_nfa A) k,
      full_choice_g5_witness_bound_le word_fuel graph_fuel m k ->
      accepting_run_g5_walk_witnesses_on_bounded_words
        word_fuel graph_fuel m k.
  Proof.
    intros word_fuel graph_fuel m k Hbound w Hall Hlen_word.
    set (n := length (accepting_run_full_choices m w)).
    destruct
      (finite_index_choice_list
        (list (quotient_component m))
        n
        (fun i walk =>
          g5_walkb word_fuel graph_fuel m walk = true /\
          g5_red_edges_on_walk word_fuel m walk <= k /\
          length walk <= S (length w)))
      as [walks [Hwalks_len Hwalks]].
    {
      intros i Hi.
      subst n.
      eapply full_choice_g5_witnesses_from_max_le; eauto.
    }
    exists
      (fun i =>
        match nth_error walks i with
        | Some walk => walk
        | None => []
        end).
    intros i Hi.
    subst n.
    destruct (Hwalks i Hi) as [walk [Hnth [_ [Hred Hlen]]]].
    rewrite Hnth. auto.
  Qed.

  Definition g5_walk_compression_bound
      (word_fuel graph_fuel : nat)
      (m : @finite_nfa A)
      (d : nat) : Prop :=
    let components := scc_quotient_with_fuel graph_fuel m in
    forall walk,
      walk <> [] ->
      Forall (fun c => In c components) walk ->
      g5_walkb word_fuel graph_fuel m walk = true ->
      exists short,
        short <> [] /\
        Forall (fun c => In c components) short /\
        g5_walkb word_fuel graph_fuel m short = true /\
        g5_red_edges_on_walk word_fuel m short <= d /\
        length short <= length walk.

  Lemma NoDup_Forall_In_length_le :
    forall (B : Type) (xs ys : list B),
      NoDup xs ->
      Forall (fun x => In x ys) xs ->
      length xs <= length ys.
  Proof.
    intros B xs ys Hnodup Hall.
    eapply NoDup_incl_length.
    - exact Hnodup.
    - intros x Hx.
      rewrite Forall_forall in Hall.
      now apply Hall.
  Qed.

  Definition quotient_component_eq_dec
      (m : @finite_nfa A)
      (c d : quotient_component m) : {c = d} + {c <> d} :=
    list_eq_dec (finite_state_eq_dec m) c d.

  Fixpoint drop_until_after_component
      (m : @finite_nfa A)
      (c : quotient_component m)
      (walk : list (quotient_component m))
      : list (quotient_component m) :=
    match walk with
    | [] => []
    | d :: walk' =>
        if quotient_component_eq_dec m c d
        then walk'
        else drop_until_after_component m c walk'
    end.

  Lemma drop_until_after_component_length_lt :
    forall (m : @finite_nfa A) c walk,
      In c walk ->
      length (drop_until_after_component m c walk) < length walk.
  Proof.
    intros m c walk.
    induction walk as [| d walk IH]; intros Hin; simpl in *.
    - contradiction.
    - destruct (quotient_component_eq_dec m c d) as [Heq | Hneq].
      + lia.
      + destruct Hin as [Hin | Hin].
        * symmetry in Hin. contradiction.
        * specialize (IH Hin). lia.
  Qed.

  Lemma drop_until_after_component_Forall :
    forall (m : @finite_nfa A) (P : quotient_component m -> Prop) c walk,
      Forall P walk ->
      Forall P (drop_until_after_component m c walk).
  Proof.
    intros m P c walk.
    induction walk as [| d walk IH]; intros Hall; simpl.
    - constructor.
    - inversion Hall as [| ? ? Hd Htail]; subst.
      destruct (quotient_component_eq_dec m c d).
      + exact Htail.
      + now apply IH.
  Qed.

  Lemma g5_walkb_from_drop_until_after_component :
    forall word_fuel graph_fuel (m : @finite_nfa A) start c walk,
      In c walk ->
      g5_walkb_from word_fuel graph_fuel m start walk = true ->
      g5_walkb_from
        word_fuel graph_fuel m c
        (drop_until_after_component m c walk) = true.
  Proof.
    intros word_fuel graph_fuel m start c walk.
    revert start c.
    induction walk as [| d walk IH]; intros start c Hin Hwalk; simpl in *.
    - contradiction.
    - destruct (quotient_component_eq_dec m c d) as [Heq | Hneq].
      + apply andb_true_iff in Hwalk as [_ Htail].
        subst d.
        exact Htail.
      + apply andb_true_iff in Hwalk as [Hedge Htail].
        destruct Hin as [Hin | Hin].
        * symmetry in Hin. contradiction.
        * now apply IH with (start := d).
  Qed.

  Lemma g5_simple_walk_reduction_from_head :
    forall word_fuel graph_fuel (m : @finite_nfa A) n c walk,
      length (c :: walk) <= n ->
      Forall
        (fun e => In e (scc_quotient_with_fuel graph_fuel m))
        (c :: walk) ->
      g5_walkb word_fuel graph_fuel m (c :: walk) = true ->
      exists short_tail,
        NoDup (c :: short_tail) /\
        Forall
          (fun e => In e (scc_quotient_with_fuel graph_fuel m))
          (c :: short_tail) /\
        Forall (fun e => In e (c :: walk)) (c :: short_tail) /\
        g5_walkb word_fuel graph_fuel m (c :: short_tail) = true /\
        length (c :: short_tail) <= length (c :: walk).
  Proof.
    intros word_fuel graph_fuel m n.
    induction n as [| n IH]; intros c walk Hlen Hall Hwalk.
    - simpl in Hlen. lia.
    - destruct (in_dec (quotient_component_eq_dec m) c walk) as [Hin | Hnotin].
      + set (trimmed := drop_until_after_component m c walk).
        assert (Htrim_len : length (c :: trimmed) <= n).
        {
          unfold trimmed.
          pose proof
            (drop_until_after_component_length_lt m c walk Hin) as Hdrop.
          simpl in *. lia.
        }
        assert (Htrim_len_original : length (c :: trimmed) <= length (c :: walk)).
        {
          unfold trimmed.
          pose proof
            (drop_until_after_component_length_lt m c walk Hin) as Hdrop.
          simpl in *. lia.
        }
        assert (Htrim_all :
          Forall
            (fun e => In e (scc_quotient_with_fuel graph_fuel m))
            (c :: trimmed)).
        {
          inversion Hall as [| ? ? Hc Htail]; subst.
          constructor.
          - exact Hc.
          - unfold trimmed.
            now apply drop_until_after_component_Forall.
        }
        assert (Htrim_origin : Forall (fun e => In e (c :: walk)) (c :: trimmed)).
        {
          constructor.
          - simpl. left. reflexivity.
          - unfold trimmed.
            apply drop_until_after_component_Forall.
            apply Forall_forall.
            intros e He. simpl. right. exact He.
        }
        assert (Htrim_walk :
          g5_walkb word_fuel graph_fuel m (c :: trimmed) = true).
        {
          simpl in Hwalk |- *.
          unfold trimmed.
          eapply g5_walkb_from_drop_until_after_component
            with (start := c); eauto.
        }
        destruct (IH c trimmed Htrim_len Htrim_all Htrim_walk)
          as [short_tail [Hnodup [Hshort_all [Hshort_origin
            [Hshort_walk Hshort_len]]]]].
        exists short_tail.
        repeat split; try assumption.
        * eapply Forall_impl.
          -- intros e He.
             rewrite Forall_forall in Htrim_origin.
             exact (Htrim_origin e He).
          -- exact Hshort_origin.
        * lia.
      + destruct walk as [| d walk'].
        * exists [].
          split.
          -- constructor; [intros [] | constructor].
          -- split.
             ++ exact Hall.
             ++ split.
                ** constructor.
                   --- simpl. left. reflexivity.
                   --- constructor.
                ** split; [exact Hwalk | lia].
        * simpl in Hwalk.
          apply andb_true_iff in Hwalk as [Hedge Htail_walk].
          inversion Hall as [| ? ? Hc Htail_all]; subst.
          assert (Htail_len : length (d :: walk') <= n).
          {
            simpl in Hlen.
            apply le_S_n in Hlen.
            exact Hlen.
          }
          destruct (IH d walk' Htail_len Htail_all Htail_walk)
            as [short_tail [Htail_nodup [Hshort_all_tail [Htail_origin
              [Hshort_tail_walk Htail_short_len]]]]].
          exists (d :: short_tail).
          repeat split.
          -- constructor.
             ++ intros Hin_tail.
                rewrite Forall_forall in Htail_origin.
                specialize (Htail_origin c Hin_tail).
                contradiction.
             ++ exact Htail_nodup.
          -- constructor; [exact Hc | exact Hshort_all_tail].
          -- constructor.
             ++ simpl. left. reflexivity.
             ++ eapply Forall_impl.
                ** intros e He. simpl. right. exact He.
                ** exact Htail_origin.
          -- simpl. rewrite Hedge. exact Hshort_tail_walk.
          -- simpl in *. lia.
  Qed.

  Lemma g5_simple_walk_reduction :
    forall word_fuel graph_fuel (m : @finite_nfa A) walk,
      walk <> [] ->
      Forall
        (fun e => In e (scc_quotient_with_fuel graph_fuel m))
        walk ->
      g5_walkb word_fuel graph_fuel m walk = true ->
      exists short,
        short <> [] /\
        NoDup short /\
        Forall
          (fun e => In e (scc_quotient_with_fuel graph_fuel m))
          short /\
        g5_walkb word_fuel graph_fuel m short = true /\
        length short <= length walk.
  Proof.
    intros word_fuel graph_fuel m walk Hnonempty Hall Hwalk.
    destruct walk as [| c walk]; [contradiction |].
    destruct
      (g5_simple_walk_reduction_from_head
        word_fuel graph_fuel m (length (c :: walk)) c walk)
      as [short_tail [Hnodup [Hshort_all [_ [Hshort_walk Hshort_len]]]]].
    - lia.
    - exact Hall.
    - exact Hwalk.
    - exists (c :: short_tail).
      repeat split; try assumption.
      discriminate.
  Qed.

  Definition g5_simple_walk_compression_bound
      (word_fuel graph_fuel : nat)
      (m : @finite_nfa A)
      (d : nat) : Prop :=
    let components := scc_quotient_with_fuel graph_fuel m in
    forall walk,
      walk <> [] ->
      Forall (fun c => In c components) walk ->
      g5_walkb word_fuel graph_fuel m walk = true ->
      exists short,
        short <> [] /\
        NoDup short /\
        Forall (fun c => In c components) short /\
        g5_walkb word_fuel graph_fuel m short = true /\
        g5_red_edges_on_walk word_fuel m short <= d /\
        length short <= length walk.

  Lemma g5_simple_walk_red_bound_from_max_le :
    forall word_fuel graph_fuel (m : @finite_nfa A) k walk,
      let components := scc_quotient_with_fuel graph_fuel m in
      NoDup walk ->
      walk <> [] ->
      Forall (fun c => In c components) walk ->
      g5_walkb word_fuel graph_fuel m walk = true ->
      max_g5_red_depth_with_fuel
        word_fuel graph_fuel m (length components) = k ->
      k <= length components ->
      g5_red_edges_on_walk word_fuel m walk <= k.
  Proof.
    intros word_fuel graph_fuel m k walk components
      Hnodup Hnonempty Hall Hwalk Hmax Hle.
    destruct (Nat.eq_dec k (length components)) as [Heq | Hneq].
    - pose proof (g5_red_edges_on_walk_le_edges word_fuel m walk) as Hred.
      pose proof
        (NoDup_Forall_In_length_le
          (quotient_component m) walk components Hnodup Hall)
        as Hlen.
      assert (Hpred : pred (length walk) <= length components).
      {
        destruct (length walk); simpl in *; lia.
      }
      rewrite Heq.
      eapply Nat.le_trans; [exact Hred | exact Hpred].
    - assert (Hlt : k < length components).
      {
        apply Nat.lt_eq_cases in Hle as [Hlt | Heq].
        - exact Hlt.
        - contradiction.
      }
      assert (Hlen_walk : length walk <= S (length components)).
      {
        pose proof
          (NoDup_Forall_In_length_le
            (quotient_component m) walk components Hnodup Hall)
          as Hlen.
        lia.
      }
      assert (Hchecker :
        g5_red_pathb_with_fuel word_fuel graph_fuel m (S k) = false).
      {
        eapply max_g5_red_depth_with_fuel_next_false; eauto.
      }
      eapply g5_red_pathb_false_bounds_walk; eauto.
  Qed.

  Lemma g5_simple_walk_compression_bound_from_max :
    forall word_fuel graph_fuel (m : @finite_nfa A) k,
      let components := scc_quotient_with_fuel graph_fuel m in
      max_g5_red_depth_with_fuel
        word_fuel graph_fuel m (length components) = k ->
      k <= length components ->
      g5_simple_walk_compression_bound word_fuel graph_fuel m k.
  Proof.
    intros word_fuel graph_fuel m k components Hmax Hle
      walk Hnonempty Hall Hwalk.
    destruct
      (g5_simple_walk_reduction
        word_fuel graph_fuel m walk Hnonempty Hall Hwalk)
      as [short [Hshort_nonempty [Hshort_nodup [Hshort_all
        [Hshort_walk Hshort_len]]]]].
    exists short.
    repeat split; try assumption.
    eapply g5_simple_walk_red_bound_from_max_le; eauto.
  Qed.

  Lemma g5_walk_compression_bound_from_simple :
    forall word_fuel graph_fuel (m : @finite_nfa A) d,
      g5_simple_walk_compression_bound word_fuel graph_fuel m d ->
      g5_walk_compression_bound word_fuel graph_fuel m d.
  Proof.
    intros word_fuel graph_fuel m d Hsimple walk Hnonempty Hall Hwalk.
    destruct (Hsimple walk Hnonempty Hall Hwalk) as
      [short [Hshort_nonempty [_Hnodup [Hshort_all [Hshort_walk
        [Hshort_red Hshort_len]]]]]].
    exists short.
    repeat split; assumption.
  Qed.

  Lemma g5_simple_walk_compression_bound_from_simple_reduction :
    forall word_fuel graph_fuel (m : @finite_nfa A) k,
      let components := scc_quotient_with_fuel graph_fuel m in
      max_g5_red_depth_with_fuel
        word_fuel graph_fuel m (length components) = k ->
      k <= length components ->
      (forall walk,
        walk <> [] ->
        Forall (fun c => In c components) walk ->
        g5_walkb word_fuel graph_fuel m walk = true ->
        exists short,
          short <> [] /\
          NoDup short /\
          Forall (fun c => In c components) short /\
          g5_walkb word_fuel graph_fuel m short = true /\
          length short <= length walk) ->
      g5_simple_walk_compression_bound word_fuel graph_fuel m k.
  Proof.
    intros word_fuel graph_fuel m k components Hmax Hle Hreduce
      walk Hnonempty Hall Hwalk.
    destruct (Hreduce walk Hnonempty Hall Hwalk) as
      [short [Hshort_nonempty [Hshort_nodup [Hshort_all
        [Hshort_walk Hshort_len]]]]].
    exists short.
    repeat split; try assumption.
    eapply g5_simple_walk_red_bound_from_max_le; eauto.
  Qed.

  Definition g5_bounded_walk_reduction
      (word_fuel graph_fuel : nat)
      (m : @finite_nfa A) : Prop :=
    let components := scc_quotient_with_fuel graph_fuel m in
    forall walk,
      walk <> [] ->
      Forall (fun c => In c components) walk ->
      g5_walkb word_fuel graph_fuel m walk = true ->
      exists short,
        short <> [] /\
        Forall (fun c => In c components) short /\
        g5_walkb word_fuel graph_fuel m short = true /\
        length short <= S (length components) /\
        length short <= length walk.

  Lemma g5_bounded_walk_reduction_from_simple_compression :
    forall word_fuel graph_fuel (m : @finite_nfa A) d,
      g5_simple_walk_compression_bound word_fuel graph_fuel m d ->
      g5_bounded_walk_reduction word_fuel graph_fuel m.
  Proof.
    intros word_fuel graph_fuel m d Hsimple walk Hnonempty Hall Hwalk.
    destruct (Hsimple walk Hnonempty Hall Hwalk) as
      [short [Hshort_nonempty [Hshort_nodup [Hshort_all
        [Hshort_walk [_ Hshort_len]]]]]].
    exists short.
    repeat split; try assumption.
    pose proof
      (NoDup_Forall_In_length_le
        (quotient_component m) short
        (scc_quotient_with_fuel graph_fuel m)
        Hshort_nodup Hshort_all)
      as Hlen.
    lia.
  Qed.

  Lemma g5_walk_compression_bound_from_bounded_reduction :
    forall word_fuel graph_fuel (m : @finite_nfa A) k,
      let components := scc_quotient_with_fuel graph_fuel m in
      max_g5_red_depth_with_fuel
        word_fuel graph_fuel m (length components) = k ->
      k <= length components ->
      g5_bounded_walk_reduction word_fuel graph_fuel m ->
      g5_walk_compression_bound word_fuel graph_fuel m k.
  Proof.
    intros word_fuel graph_fuel m k components Hmax Hle Hreduce
      walk Hnonempty Hall Hwalk.
    destruct (Hreduce walk Hnonempty Hall Hwalk) as
      [short [Hshort_nonempty [Hshort_all [Hshort_walk
        [Hshort_len_components Hshort_len]]]]].
    exists short.
    repeat split; try assumption.
    destruct (Nat.eq_dec k (length components)) as [Heq | Hneq].
    - pose proof (g5_red_edges_on_walk_le_edges word_fuel m short) as Hred.
      pose proof (Nat.pred_le_mono _ _ Hshort_len_components) as Hpred.
      simpl in Hpred.
      rewrite Heq.
      eapply Nat.le_trans; [exact Hred | exact Hpred].
    - assert (Hlt : k < length components).
      {
        apply Nat.lt_eq_cases in Hle as [Hlt | Heq].
        - exact Hlt.
        - contradiction.
      }
      assert (Hchecker :
        g5_red_pathb_with_fuel word_fuel graph_fuel m (S k) = false).
      {
        eapply max_g5_red_depth_with_fuel_next_false; eauto.
      }
      eapply g5_red_pathb_false_bounds_walk; eauto.
  Qed.

  Lemma accepting_run_g5_walk_witnesses_on_alphabet_from_compression :
    forall word_fuel graph_fuel (m : @finite_nfa A) d,
      fnfa_well_formed m ->
      1 <= graph_fuel ->
      g5_walk_compression_bound word_fuel graph_fuel m d ->
      accepting_run_g5_walk_witnesses_on_alphabet word_fuel m d.
  Proof.
    intros word_fuel graph_fuel m d Hwf Hfuel Hcompress w Hall.
    set (n := length (accepting_run_full_choices m w)).
    destruct
      (finite_index_choice_list
        (list (quotient_component m))
        n
        (fun i short =>
          short <> [] /\
          Forall
            (fun c => In c (scc_quotient_with_fuel graph_fuel m))
            short /\
          g5_walkb word_fuel graph_fuel m short = true /\
          g5_red_edges_on_walk word_fuel m short <= d /\
          length short <= S (length w)))
      as [walks [Hwalks_len Hwalks]].
    {
      intros i Hi.
      subst n.
      destruct
        (component_walk_for_accepting_run_full_choice
          word_fuel graph_fuel m w i Hwf Hall Hi Hfuel)
        as [choices [start_idx [tail [q0 [qf [c0 [cf [walk Hdata]]]]]]]].
      destruct Hdata as [_ Hdata].
      destruct Hdata as [_ Hdata].
      destruct Hdata as [_ Hdata].
      destruct Hdata as [_ Hdata].
      destruct Hdata as [_ Hdata].
      destruct Hdata as [_ Hdata].
      destruct Hdata as [_ Hdata].
      destruct Hdata as [_ Hdata].
      destruct Hdata as [Hnonempty Hdata].
      destruct Hdata as [Hall_walk Hdata].
      destruct Hdata as [Hlen_walk Hdata].
      destruct Hdata as [_ Hdata].
      destruct Hdata as [_ Hdata].
      destruct Hdata as [Hwalk _].
      destruct (Hcompress walk Hnonempty Hall_walk Hwalk) as
        [short [Hshort_nonempty [Hshort_all [Hshort_walk
          [Hshort_red Hshort_len]]]]].
      exists short.
      repeat split; auto.
      lia.
    }
    exists
      (fun i =>
        match nth_error walks i with
        | Some walk => walk
        | None => []
        end).
    intros i Hi.
    subst n.
    destruct (Hwalks i Hi) as
      [walk [Hnth [_ [_ [_ [Hred Hlen]]]]]].
    rewrite Hnth. auto.
  Qed.

  Theorem degree_at_most_on_alphabet_from_compression_and_payloads :
    forall word_fuel graph_fuel (m : @finite_nfa A)
      (Payload : Type) payloads d c,
      fnfa_well_formed m ->
      1 <= graph_fuel ->
      NoDup payloads ->
      length payloads <= c ->
      g5_walk_compression_bound word_fuel graph_fuel m d ->
      accepting_run_g5_payload_injection_on_alphabet
        word_fuel m Payload payloads d ->
      degree_at_most_on_alphabet m d.
  Proof.
    intros word_fuel graph_fuel m Payload payloads d c
      Hwf Hfuel Hnodup Hpayload_bound Hcompress Hpayloads.
    eapply degree_at_most_on_alphabet_from_run_g5_witnesses_and_payloads.
    - exact Hnodup.
    - exact Hpayload_bound.
    - eapply accepting_run_g5_walk_witnesses_on_alphabet_from_compression;
        eauto.
    - exact Hpayloads.
  Qed.

  Theorem degree_at_most_on_alphabet_from_compression_and_payload_function :
    forall word_fuel graph_fuel (m : @finite_nfa A)
      (Payload : Type) payloads d c,
      fnfa_well_formed m ->
      1 <= graph_fuel ->
      NoDup payloads ->
      length payloads <= c ->
      g5_walk_compression_bound word_fuel graph_fuel m d ->
      accepting_run_g5_payload_function_on_alphabet
        word_fuel m Payload payloads d ->
      degree_at_most_on_alphabet m d.
  Proof.
    intros word_fuel graph_fuel m Payload payloads d c
      Hwf Hfuel Hnodup Hpayload_bound Hcompress Hpayloads.
    eapply degree_at_most_on_alphabet_from_compression_and_payloads;
      eauto.
    now apply accepting_run_g5_payload_injection_from_function.
  Qed.

  Lemma g5_edgeb_sound :
    forall word_fuel graph_fuel (m : @finite_nfa A) c d,
      g5_edgeb word_fuel graph_fuel m c d = true ->
      (exists p q v,
        In p c /\
        In q d /\
        IDA_pair m p q v) \/
      (exists p q w,
        In p c /\
        In q d /\
        finite_delta_star m p w q).
  Proof.
    intros word_fuel graph_fuel m c d H.
    unfold g5_edgeb in H.
    apply orb_true_iff in H as [Hred | Hplain].
    - left. now apply g5_red_edgeb_sound in Hred.
    - right. now apply g5_plain_edgeb_sound in Hplain.
  Qed.

  Theorem g5_red_edgeb_degree_at_least_1 :
    forall word_fuel (m : @finite_nfa A) c d,
      g5_red_edgeb word_fuel m c d = true ->
      degree_at_least (fnfa_base m) 1.
  Proof.
    intros word_fuel m c d H.
    destruct (g5_red_edgeb_sound word_fuel m c d H) as
      [p [q [v [_ [_ Hpair]]]]].
    apply IDA_d_polynomial_growth_lower_bound.
    apply IDA_d_one_iff_IDA.
    exists p, q, v. exact Hpair.
  Qed.

  Lemma g5_red_pathb_from_sound_chain :
    forall path_fuel word_fuel graph_fuel
        (m : @finite_nfa A) components red_count c,
      components_connected m components ->
      In c components ->
      g5_red_pathb_from
        path_fuel word_fuel graph_fuel m components (S red_count) c = true ->
      exists p r s w,
        In p c /\
        finite_delta_star m p w r /\
        IDA_chain m (S red_count) r s.
  Proof.
    induction path_fuel as [| path_fuel IH];
      intros word_fuel graph_fuel m components red_count c
        Hcomponents Hc Hpath.
    - simpl in Hpath. discriminate.
    - simpl in Hpath.
      apply existsb_exists in Hpath as [target [Htarget Hstep]].
      destruct (g5_edgeb word_fuel graph_fuel m c target) eqn:Hedge;
        try discriminate.
      destruct (g5_red_edgeb word_fuel m c target) eqn:Hred.
      + destruct
          (g5_red_edgeb_sound word_fuel m c target Hred)
          as [p [q [v [Hp [Hq Hpair]]]]].
        destruct red_count as [| red_count'].
        * exists p, p, q, [].
          split; [exact Hp | split].
          -- constructor.
          -- now apply IDA_chain_one with (v := v).
        * destruct
            (IH
               word_fuel
               graph_fuel
               m
               components
               red_count'
               target
               Hcomponents
               Htarget
               Hstep)
            as [p_tail [r_tail [s_tail [w_tail
              [Hp_tail [Hprefix Hchain]]]]]].
          pose proof (Hcomponents target Htarget) as Htarget_connected.
          destruct
            (component_connected_path
               m target q p_tail Htarget_connected Hq Hp_tail)
            as [u Hq_to_tail].
          assert (Hconnector :
            finite_delta_star m q (u ++ w_tail) r_tail).
          {
            eapply path_from_app; eauto.
          }
          exists p, p, s_tail, [].
          split; [exact Hp | split].
          -- constructor.
          -- eapply IDA_chain_cons
               with (s := q) (v := v) (u := u ++ w_tail) (r' := r_tail).
             ++ exact Hpair.
             ++ exact Hconnector.
             ++ exact Hchain.
      + assert (Hplain : g5_plain_edgeb graph_fuel m c target = true).
        {
          unfold g5_edgeb in Hedge.
          rewrite Hred in Hedge.
          simpl in Hedge.
          exact Hedge.
        }
        destruct
          (g5_plain_edgeb_sound graph_fuel m c target Hplain)
          as [p [q [u [Hp [Hq Hplain_path]]]]].
        destruct
          (IH
             word_fuel
             graph_fuel
             m
             components
             red_count
             target
             Hcomponents
             Htarget
             Hstep)
          as [p_tail [r_tail [s_tail [w_tail
            [Hp_tail [Hprefix Hchain]]]]]].
        pose proof (Hcomponents target Htarget) as Htarget_connected.
        destruct
          (component_connected_path
             m target q p_tail Htarget_connected Hq Hp_tail)
          as [v Hq_to_tail].
        assert (Hp_to_tail :
          finite_delta_star m p (u ++ v) p_tail).
        {
          eapply path_from_app; eauto.
        }
        assert (Hp_to_chain :
          finite_delta_star m p ((u ++ v) ++ w_tail) r_tail).
        {
          eapply path_from_app; eauto.
        }
        exists p, r_tail, s_tail, ((u ++ v) ++ w_tail).
        repeat split; auto.
  Qed.

  Theorem g5_red_pathb_with_fuel_degree_at_least :
    forall word_fuel graph_fuel (m : @finite_nfa A) d,
      g5_red_pathb_with_fuel word_fuel graph_fuel m (S d) = true ->
      degree_at_least (fnfa_base m) (S d).
  Proof.
    intros word_fuel graph_fuel m d H.
    unfold g5_red_pathb_with_fuel in H.
    set (components := scc_quotient_with_fuel graph_fuel m) in H.
    apply existsb_exists in H as [c [Hc Hpath]].
    destruct
      (g5_red_pathb_from_sound_chain
         (length components)
         word_fuel
         graph_fuel
         m
         components
         d
         c)
      as [p [r [s [w [_ [_ Hchain]]]]]]; auto.
    - unfold components_connected.
      intros c' Hc'.
      subst components.
      now apply
        (scc_quotient_with_fuel_component_connected graph_fuel m c').
    - apply IDA_d_polynomial_growth_lower_bound.
      exists r, s. exact Hchain.
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

  Lemma idab_chainb_sound :
    forall fuel (m : @finite_nfa A) d r s,
      idab_chainb fuel m d r s = true ->
      IDA_chain m d r s.
  Proof.
    intros fuel m d.
    induction d as [| d IH]; intros r s H.
    - simpl in H. discriminate.
    - destruct d as [| d'].
      + simpl in H.
        destruct (idab_pairb_sound fuel m r s H) as [v Hpair].
        now apply IDA_chain_one with (v := v).
      + simpl in H.
        apply existsb_exists in H as [s0 [_ Hs0]].
        apply andb_true_iff in Hs0 as [Hpair Hnext].
        apply existsb_exists in Hnext as [r' [_ Hr']].
        apply existsb_exists in Hr' as [u [_ Hu]].
        apply andb_true_iff in Hu as [Hpath Htail].
        destruct (idab_pairb_sound fuel m r s0 Hpair) as [v Hpair_prop].
        eapply IDA_chain_cons with (s := s0) (v := v) (u := u) (r' := r').
        * exact Hpair_prop.
        * now apply pathb_sound.
        * now apply IH.
  Qed.

  Lemma idab_chainb_graph_sound :
    forall word_fuel graph_fuel (m : @finite_nfa A) d r s,
      idab_chainb_graph word_fuel graph_fuel m d r s = true ->
      IDA_chain m d r s.
  Proof.
    intros word_fuel graph_fuel m d.
    induction d as [| d IH]; intros r s H.
    - simpl in H. discriminate.
    - destruct d as [| d'].
      + simpl in H.
        destruct (idab_pairb_sound word_fuel m r s H) as [v Hpair].
        now apply IDA_chain_one with (v := v).
      + simpl in H.
        apply existsb_exists in H as [s0 [_ Hs0]].
        apply andb_true_iff in Hs0 as [Hpair Hnext].
        apply existsb_exists in Hnext as [r' [_ Hr']].
        apply andb_true_iff in Hr' as [Hreach Htail].
        destruct (idab_pairb_sound word_fuel m r s0 Hpair) as [v Hpair_prop].
        destruct (reachable_stateb_sound graph_fuel m s0 r' Hreach)
          as [u Hpath].
        eapply IDA_chain_cons with (s := s0) (v := v) (u := u) (r' := r').
        * exact Hpair_prop.
        * exact Hpath.
        * now apply IH.
  Qed.

  Theorem idab_d_with_fuel_sound :
    forall fuel (m : @finite_nfa A) d,
      idab_d_with_fuel fuel m d = true ->
      IDA_d m d.
  Proof.
    intros fuel m d H.
    destruct d as [| d].
    - exact I.
    - simpl in H.
      apply existsb_exists in H as [r [_ Hr]].
      apply existsb_exists in Hr as [s [_ Hs]].
      exists r, s.
      now apply idab_chainb_sound with (fuel := fuel).
  Qed.

  Theorem idab_d_graph_with_fuel_sound :
    forall word_fuel graph_fuel (m : @finite_nfa A) d,
      idab_d_graph_with_fuel word_fuel graph_fuel m d = true ->
      IDA_d m d.
  Proof.
    intros word_fuel graph_fuel m d H.
    destruct d as [| d].
    - exact I.
    - simpl in H.
      apply existsb_exists in H as [r [_ Hr]].
      apply existsb_exists in Hr as [s [_ Hs]].
      exists r, s.
      now apply idab_chainb_graph_sound
        with (word_fuel := word_fuel) (graph_fuel := graph_fuel).
  Qed.

  Theorem idab_with_fuel_sound_IDA_d_1 :
    forall fuel (m : @finite_nfa A),
      idab_with_fuel fuel m = true ->
      IDA_d m 1.
  Proof.
    intros fuel m H.
    apply IDA_d_one_iff_IDA.
    now apply idab_with_fuel_sound with (fuel := fuel).
  Qed.

  Theorem idab_with_fuel_degree_at_least_1 :
    forall fuel (m : @finite_nfa A),
      idab_with_fuel fuel m = true ->
      degree_at_least (fnfa_base m) 1.
  Proof.
    intros fuel m H.
    apply IDA_d_polynomial_growth_lower_bound.
    now apply idab_with_fuel_sound_IDA_d_1 with (fuel := fuel).
  Qed.

  Theorem idab_d_with_fuel_degree_at_least :
    forall fuel (m : @finite_nfa A) d,
      idab_d_with_fuel fuel m (S d) = true ->
      degree_at_least (fnfa_base m) (S d).
  Proof.
    intros fuel m d H.
    apply IDA_d_polynomial_growth_lower_bound.
    now apply idab_d_with_fuel_sound with (fuel := fuel).
  Qed.

  Theorem idab_d_graph_with_fuel_degree_at_least :
    forall word_fuel graph_fuel (m : @finite_nfa A) d,
      idab_d_graph_with_fuel word_fuel graph_fuel m (S d) = true ->
      degree_at_least (fnfa_base m) (S d).
  Proof.
    intros word_fuel graph_fuel m d H.
    apply IDA_d_polynomial_growth_lower_bound.
    now apply idab_d_graph_with_fuel_sound
      with (word_fuel := word_fuel) (graph_fuel := graph_fuel).
  Qed.

  Theorem g5_red_self_edgeb_degree_at_least :
    forall word_fuel graph_fuel (m : @finite_nfa A) c d,
      In c (scc_quotient_with_fuel graph_fuel m) ->
      g5_red_edgeb word_fuel m c c = true ->
      degree_at_least (fnfa_base m) (S d).
  Proof.
    intros word_fuel graph_fuel m c d Hc Hred.
    destruct (g5_red_edgeb_sound word_fuel m c c Hred) as
      [p [q [v [Hp [Hq Hpair]]]]].
    pose proof
      (scc_quotient_with_fuel_component_connected graph_fuel m c Hc)
      as Hconnected.
    destruct (component_connected_path m c q p Hconnected Hq Hp)
      as [u Hconnector].
    apply IDA_d_polynomial_growth_lower_bound.
    exists p, q.
    eapply IDA_pair_connector_chain; eauto.
  Qed.

  Lemma IDA_pair_connector_EDA :
    forall (m : @finite_nfa A) p q v u,
      IDA_pair m p q v ->
      finite_delta_star m q u p ->
      EDA m.
  Proof.
    intros m p q v u Hpair Hconnector.
    destruct Hpair as [Hneq [Huseful_p [_Huseful_q [Hpp [Hpq Hqq]]]]].
    exists p, (v ++ v ++ u).
    repeat split.
    - exact Huseful_p.
    - eapply path_from_app.
      + exact Hpp.
      + eapply path_from_app; eauto.
    - pose proof (path_runs_between_positive m p v p Hpp) as Hpp_pos.
      pose proof (path_runs_between_positive m p v q Hpq) as Hpq_pos.
      assert (Hp_tail : finite_delta_star m p (v ++ u) p).
      {
        eapply path_from_app; eauto.
      }
      assert (Hq_tail : finite_delta_star m q (v ++ u) p).
      {
        eapply path_from_app; eauto.
      }
      pose proof (path_runs_between_positive m p (v ++ u) p Hp_tail)
        as Hp_tail_pos.
      pose proof (path_runs_between_positive m q (v ++ u) p Hq_tail)
        as Hq_tail_pos.
      pose proof
        (runs_between_app_ge_two m p v p q (v ++ u) p Hneq)
        as Htwo.
      unfold da_from_to in *. lia.
  Qed.

  Theorem g5_red_self_edgeb_EDA :
    forall word_fuel graph_fuel (m : @finite_nfa A) c,
      In c (scc_quotient_with_fuel graph_fuel m) ->
      g5_red_edgeb word_fuel m c c = true ->
      EDA m.
  Proof.
    intros word_fuel graph_fuel m c Hc Hred.
    destruct (g5_red_edgeb_sound word_fuel m c c Hred) as
      [p [q [v [Hp [Hq Hpair]]]]].
    pose proof
      (scc_quotient_with_fuel_component_connected graph_fuel m c Hc)
      as Hconnected.
    destruct (component_connected_path m c q p Hconnected Hq Hp)
      as [u Hconnector].
    eapply IDA_pair_connector_EDA; eauto.
  Qed.

  Theorem g5_has_red_self_loopb_degree_at_least :
    forall word_fuel graph_fuel (m : @finite_nfa A) d,
      g5_has_red_self_loopb word_fuel graph_fuel m = true ->
      degree_at_least (fnfa_base m) (S d).
  Proof.
    intros word_fuel graph_fuel m d H.
    unfold g5_has_red_self_loopb in H.
    apply existsb_exists in H as [c [Hc Hred]].
    eapply g5_red_self_edgeb_degree_at_least; eauto.
  Qed.

  Theorem g5_has_red_self_loopb_EDA :
    forall word_fuel graph_fuel (m : @finite_nfa A),
      g5_has_red_self_loopb word_fuel graph_fuel m = true ->
      EDA m.
  Proof.
    intros word_fuel graph_fuel m H.
    unfold g5_has_red_self_loopb in H.
    apply existsb_exists in H as [c [Hc Hred]].
    eapply g5_red_self_edgeb_EDA; eauto.
  Qed.

  Theorem no_EDA_g5_has_red_self_loopb_false :
    forall word_fuel graph_fuel (m : @finite_nfa A),
      no_EDA m ->
      g5_has_red_self_loopb word_fuel graph_fuel m = false.
  Proof.
    intros word_fuel graph_fuel m Hno.
    destruct (g5_has_red_self_loopb word_fuel graph_fuel m) eqn:Hloop;
      auto.
    exfalso. apply Hno.
    now apply g5_has_red_self_loopb_EDA
      with (word_fuel := word_fuel) (graph_fuel := graph_fuel).
  Qed.

  Theorem no_EDA_edab_with_fuel_false :
    forall fuel (m : @finite_nfa A),
      no_EDA m ->
      edab_with_fuel fuel m = false.
  Proof.
    intros fuel m Hno.
    destruct (edab_with_fuel fuel m) eqn:Heda; auto.
    exfalso. apply Hno.
    now apply edab_with_fuel_sound with (fuel := fuel).
  Qed.

  Theorem no_EDA_ambiguity_growth_g5_lower_bound_polynomial_branch :
    forall word_fuel graph_fuel (m : @finite_nfa A),
      no_EDA m ->
      ambiguity_growth_g5_lower_bound_with_fuel word_fuel graph_fuel m =
        GrowthPolynomialLowerBound
          (max_g5_red_depth_with_fuel
             word_fuel
             graph_fuel
             m
             (length (scc_quotient_with_fuel graph_fuel m))).
  Proof.
    intros word_fuel graph_fuel m Hno.
    unfold ambiguity_growth_g5_lower_bound_with_fuel.
    rewrite (no_EDA_edab_with_fuel_false word_fuel m Hno).
    rewrite (no_EDA_g5_has_red_self_loopb_false word_fuel graph_fuel m Hno).
    reflexivity.
  Qed.

  Theorem g5_has_red_self_loopb_exponentially_ambiguous :
    forall word_fuel graph_fuel (m : @finite_nfa A),
      g5_has_red_self_loopb word_fuel graph_fuel m = true ->
      exponentially_ambiguous (fnfa_base m).
  Proof.
    intros word_fuel graph_fuel m H.
    apply EDA_exponentially_ambiguous.
    now apply g5_has_red_self_loopb_EDA
      with (word_fuel := word_fuel) (graph_fuel := graph_fuel).
  Qed.

  Lemma no_EDA_useful_loop_runs_at_most_one :
    forall (m : @finite_nfa A) q v,
      no_EDA m ->
      finite_useful m q ->
      finite_delta_star m q v q ->
      da_from_to m q v q <= 1.
  Proof.
    intros m q v Hno Huseful Hloop.
    destruct (le_lt_dec 2 (da_from_to m q v q)) as [Htwo | Hlt].
    - exfalso. apply Hno.
      exists q, v. repeat split; assumption.
    - lia.
  Qed.

  Lemma no_EDA_useful_loop_choices_unique :
    forall (m : @finite_nfa A) q v c1 c2,
      no_EDA m ->
      finite_useful m q ->
      In c1 (run_choices_between m q v q) ->
      In c2 (run_choices_between m q v q) ->
      c1 = c2.
  Proof.
    intros m q v c1 c2 Hno Huseful Hc1 Hc2.
    destruct (list_eq_dec Nat.eq_dec c1 c2) as [Heq | Hneq];
      [exact Heq |].
    exfalso. apply Hno.
    eapply EDA_from_two_distinct_loop_choices
      with (q := q) (v := v) (c1 := c1) (c2 := c2);
      assumption.
  Qed.

  Lemma no_EDA_trim_loop_runs_at_most_one :
    forall (m : @finite_nfa A) q v,
      no_EDA m ->
      (forall r, In r (fnfa_states m) -> finite_useful m r) ->
      In q (fnfa_states m) ->
      finite_delta_star m q v q ->
      da_from_to m q v q <= 1.
  Proof.
    intros m q v Hno Htrim Hq Hloop.
    destruct (le_lt_dec 2 (da_from_to m q v q)) as [Htwo | Hlt].
    - exfalso. apply Hno.
      exists q, v. repeat split.
      + apply Htrim. exact Hq.
      + exact Hloop.
      + exact Htwo.
    - lia.
  Qed.

  Lemma no_EDA_fnfa_trim_loop_runs_at_most_one :
    forall (m : @finite_nfa A) q v,
      no_EDA m ->
      @fnfa_trim A m ->
      In q (fnfa_states m) ->
      finite_delta_star m q v q ->
      da_from_to m q v q <= 1.
  Proof.
    intros m q v Hno Htrim Hq Hloop.
    eapply no_EDA_useful_loop_runs_at_most_one.
    - exact Hno.
    - exact (Htrim q Hq).
    - exact Hloop.
  Qed.

  Lemma no_EDA_loop_runs_at_most_one_from_positive_context :
    forall (m : @finite_nfa A) q v w_in w_out,
      no_EDA m ->
      0 < start_runs_to m w_in q ->
      0 < accepting_runs_from (fnfa_base m) q w_out ->
      finite_delta_star m q v q ->
      da_from_to m q v q <= 1.
  Proof.
    intros m q v w_in w_out Hno Hin Hout Hloop.
    eapply no_EDA_useful_loop_runs_at_most_one; eauto.
    eapply useful_state_from_positive_tests; eauto.
  Qed.

  Lemma max_g5_red_depth_with_fuel_sound_positive :
    forall word_fuel graph_fuel (m : @finite_nfa A) max_d d,
      max_g5_red_depth_with_fuel word_fuel graph_fuel m max_d = S d ->
      degree_at_least (fnfa_base m) (S d).
  Proof.
    intros word_fuel graph_fuel m max_d.
    induction max_d as [| max_d IH]; intros d Hmax.
    - simpl in Hmax. discriminate.
    - change
        ((if g5_red_pathb_with_fuel word_fuel graph_fuel m (S max_d)
          then S max_d
          else max_g5_red_depth_with_fuel word_fuel graph_fuel m max_d)
          = S d) in Hmax.
      destruct (g5_red_pathb_with_fuel word_fuel graph_fuel m (S max_d))
        eqn:Hhit.
      + inversion Hmax; subst.
        now apply g5_red_pathb_with_fuel_degree_at_least
          with (word_fuel := word_fuel) (graph_fuel := graph_fuel).
      + now apply IH.
  Qed.

  Theorem ambiguity_growth_g5_lower_bound_with_fuel_sound_polynomial :
    forall word_fuel graph_fuel (m : @finite_nfa A) d,
      ambiguity_growth_g5_lower_bound_with_fuel word_fuel graph_fuel m =
        GrowthPolynomialLowerBound (S d) ->
      degree_at_least (fnfa_base m) (S d).
  Proof.
    intros word_fuel graph_fuel m d H.
    unfold ambiguity_growth_g5_lower_bound_with_fuel in H.
    set (components := scc_quotient_with_fuel graph_fuel m) in H.
    destruct
      (edab_with_fuel word_fuel m ||
       g5_has_red_self_loopb word_fuel graph_fuel m);
      try discriminate.
    injection H as Hmax.
    eapply max_g5_red_depth_with_fuel_sound_positive.
    exact Hmax.
  Qed.

  Theorem exact_polynomial_degree_on_alphabet_from_g5_lower_bound_and_upper :
    forall word_fuel graph_fuel (m : @finite_nfa A) d,
      ambiguity_growth_g5_lower_bound_with_fuel word_fuel graph_fuel m =
        GrowthPolynomialLowerBound (S d) ->
      degree_at_most_on_alphabet m (S d) ->
      exact_polynomial_degree_on_alphabet m (S d).
  Proof.
    intros word_fuel graph_fuel m d Hlower Hupper.
    split.
    - eapply ambiguity_growth_g5_lower_bound_with_fuel_sound_polynomial; eauto.
    - exact Hupper.
  Qed.

  Theorem exact_polynomial_degree_on_alphabet_from_g5_lower_bound_and_occurrence_codes :
    forall word_fuel graph_fuel (m : @finite_nfa A) (Code : Type) d c,
      ambiguity_growth_g5_lower_bound_with_fuel word_fuel graph_fuel m =
        GrowthPolynomialLowerBound (S d) ->
      accepting_endpoint_occurrence_codes_upper_on_alphabet m Code (S d) c ->
      exact_polynomial_degree_on_alphabet m (S d).
  Proof.
    intros word_fuel graph_fuel m Code d c Hlower Hcodes.
    apply exact_polynomial_degree_on_alphabet_from_g5_lower_bound_and_upper
      with (word_fuel := word_fuel) (graph_fuel := graph_fuel).
    - exact Hlower.
    - eapply degree_at_most_on_alphabet_from_occurrence_codes.
      exact Hcodes.
  Qed.

  Theorem exact_polynomial_degree_on_alphabet_from_g5_lower_bound_and_polynomial_signatures :
    forall word_fuel graph_fuel (m : @finite_nfa A)
      (Payload : Type) payloads d c,
      ambiguity_growth_g5_lower_bound_with_fuel word_fuel graph_fuel m =
        GrowthPolynomialLowerBound (S d) ->
      accepting_endpoint_polynomial_signatures_on_alphabet
        m Payload payloads (S d) c ->
      exact_polynomial_degree_on_alphabet m (S d).
  Proof.
    intros word_fuel graph_fuel m Payload payloads d c Hlower Hsignatures.
    apply exact_polynomial_degree_on_alphabet_from_g5_lower_bound_and_upper
      with (word_fuel := word_fuel) (graph_fuel := graph_fuel).
    - exact Hlower.
    - eapply degree_at_most_on_alphabet_from_polynomial_signatures.
      exact Hsignatures.
  Qed.

  Theorem exact_polynomial_degree_on_alphabet_from_g5_lower_bound_and_g5_walk_signatures :
    forall word_fuel graph_fuel (m : @finite_nfa A)
      (Payload : Type) payloads d c,
      ambiguity_growth_g5_lower_bound_with_fuel word_fuel graph_fuel m =
        GrowthPolynomialLowerBound (S d) ->
      accepting_endpoint_g5_walk_signatures_on_alphabet
        word_fuel m Payload payloads (S d) c ->
      exact_polynomial_degree_on_alphabet m (S d).
  Proof.
    intros word_fuel graph_fuel m Payload payloads d c Hlower Hsignatures.
    apply exact_polynomial_degree_on_alphabet_from_g5_lower_bound_and_upper
      with (word_fuel := word_fuel) (graph_fuel := graph_fuel).
    - exact Hlower.
    - eapply degree_at_most_on_alphabet_from_g5_walk_signatures.
      exact Hsignatures.
  Qed.

  Theorem exact_polynomial_degree_on_alphabet_from_g5_lower_bound_and_run_g5_walk_signatures :
    forall word_fuel graph_fuel (m : @finite_nfa A)
      (Payload : Type) payloads d c,
      ambiguity_growth_g5_lower_bound_with_fuel word_fuel graph_fuel m =
        GrowthPolynomialLowerBound (S d) ->
      accepting_run_g5_walk_signatures_on_alphabet
        word_fuel m Payload payloads (S d) c ->
      exact_polynomial_degree_on_alphabet m (S d).
  Proof.
    intros word_fuel graph_fuel m Payload payloads d c Hlower Hsignatures.
    apply exact_polynomial_degree_on_alphabet_from_g5_lower_bound_and_upper
      with (word_fuel := word_fuel) (graph_fuel := graph_fuel).
    - exact Hlower.
    - eapply degree_at_most_on_alphabet_from_run_g5_walk_signatures.
      exact Hsignatures.
  Qed.

  Theorem exact_polynomial_degree_on_alphabet_from_max_g5_depth_and_upper :
    forall word_fuel graph_fuel (m : @finite_nfa A) max_d d,
      max_g5_red_depth_with_fuel word_fuel graph_fuel m max_d = S d ->
      degree_at_most_on_alphabet m (S d) ->
      exact_polynomial_degree_on_alphabet m (S d).
  Proof.
    intros word_fuel graph_fuel m max_d d Hdepth Hupper.
    split.
    - eapply max_g5_red_depth_with_fuel_sound_positive; eauto.
    - exact Hupper.
  Qed.

  Theorem exact_polynomial_degree_on_alphabet_from_max_g5_depth_and_occurrence_codes :
    forall word_fuel graph_fuel (m : @finite_nfa A)
      (Code : Type) max_d d c,
      max_g5_red_depth_with_fuel word_fuel graph_fuel m max_d = S d ->
      accepting_endpoint_occurrence_codes_upper_on_alphabet m Code (S d) c ->
      exact_polynomial_degree_on_alphabet m (S d).
  Proof.
    intros word_fuel graph_fuel m Code max_d d c Hdepth Hcodes.
    apply exact_polynomial_degree_on_alphabet_from_max_g5_depth_and_upper
      with (word_fuel := word_fuel) (graph_fuel := graph_fuel)
           (max_d := max_d).
    - exact Hdepth.
    - eapply degree_at_most_on_alphabet_from_occurrence_codes.
      exact Hcodes.
  Qed.

  Theorem exact_polynomial_degree_on_alphabet_from_max_g5_depth_and_polynomial_signatures :
    forall word_fuel graph_fuel (m : @finite_nfa A)
      (Payload : Type) payloads max_d d c,
      max_g5_red_depth_with_fuel word_fuel graph_fuel m max_d = S d ->
      accepting_endpoint_polynomial_signatures_on_alphabet
        m Payload payloads (S d) c ->
      exact_polynomial_degree_on_alphabet m (S d).
  Proof.
    intros word_fuel graph_fuel m Payload payloads max_d d c Hdepth Hsignatures.
    apply exact_polynomial_degree_on_alphabet_from_max_g5_depth_and_upper
      with (word_fuel := word_fuel) (graph_fuel := graph_fuel)
           (max_d := max_d).
    - exact Hdepth.
    - eapply degree_at_most_on_alphabet_from_polynomial_signatures.
      exact Hsignatures.
  Qed.

  Theorem exact_polynomial_degree_on_alphabet_from_max_g5_depth_and_g5_walk_signatures :
    forall word_fuel graph_fuel (m : @finite_nfa A)
      (Payload : Type) payloads max_d d c,
      max_g5_red_depth_with_fuel word_fuel graph_fuel m max_d = S d ->
      accepting_endpoint_g5_walk_signatures_on_alphabet
        word_fuel m Payload payloads (S d) c ->
      exact_polynomial_degree_on_alphabet m (S d).
  Proof.
    intros word_fuel graph_fuel m Payload payloads max_d d c Hdepth Hsignatures.
    apply exact_polynomial_degree_on_alphabet_from_max_g5_depth_and_upper
      with (word_fuel := word_fuel) (graph_fuel := graph_fuel)
           (max_d := max_d).
    - exact Hdepth.
    - eapply degree_at_most_on_alphabet_from_g5_walk_signatures.
      exact Hsignatures.
  Qed.

  Theorem exact_polynomial_degree_on_alphabet_from_max_g5_depth_and_run_g5_walk_signatures :
    forall word_fuel graph_fuel (m : @finite_nfa A)
      (Payload : Type) payloads max_d d c,
      max_g5_red_depth_with_fuel word_fuel graph_fuel m max_d = S d ->
      accepting_run_g5_walk_signatures_on_alphabet
        word_fuel m Payload payloads (S d) c ->
      exact_polynomial_degree_on_alphabet m (S d).
  Proof.
    intros word_fuel graph_fuel m Payload payloads max_d d c Hdepth Hsignatures.
    apply exact_polynomial_degree_on_alphabet_from_max_g5_depth_and_upper
      with (word_fuel := word_fuel) (graph_fuel := graph_fuel)
           (max_d := max_d).
    - exact Hdepth.
    - eapply degree_at_most_on_alphabet_from_run_g5_walk_signatures.
      exact Hsignatures.
  Qed.

  Theorem exact_polynomial_degree_on_alphabet_from_max_g5_depth_and_run_g5_witnesses :
    forall word_fuel graph_fuel (m : @finite_nfa A)
      (Payload : Type) payloads max_d d c,
      max_g5_red_depth_with_fuel word_fuel graph_fuel m max_d = S d ->
      NoDup payloads ->
      length payloads <= c ->
      accepting_run_g5_walk_witnesses_on_alphabet word_fuel m (S d) ->
      accepting_run_g5_payload_injection_on_alphabet
        word_fuel m Payload payloads (S d) ->
      exact_polynomial_degree_on_alphabet m (S d).
  Proof.
    intros word_fuel graph_fuel m Payload payloads max_d d c
      Hdepth Hnodup Hpayload_bound Hwalks Hpayloads.
    apply exact_polynomial_degree_on_alphabet_from_max_g5_depth_and_upper
      with (word_fuel := word_fuel) (graph_fuel := graph_fuel)
           (max_d := max_d).
    - exact Hdepth.
    - eapply degree_at_most_on_alphabet_from_run_g5_witnesses_and_payloads;
        eauto.
  Qed.

  Theorem exact_polynomial_degree_on_alphabet_from_max_g5_depth_and_compression :
    forall word_fuel graph_fuel (m : @finite_nfa A)
      (Payload : Type) payloads max_d d c,
      max_g5_red_depth_with_fuel word_fuel graph_fuel m max_d = S d ->
      fnfa_well_formed m ->
      1 <= graph_fuel ->
      NoDup payloads ->
      length payloads <= c ->
      g5_walk_compression_bound word_fuel graph_fuel m (S d) ->
      accepting_run_g5_payload_injection_on_alphabet
        word_fuel m Payload payloads (S d) ->
      exact_polynomial_degree_on_alphabet m (S d).
  Proof.
    intros word_fuel graph_fuel m Payload payloads max_d d c
      Hdepth Hwf Hfuel Hnodup Hpayload_bound Hcompress Hpayloads.
    apply exact_polynomial_degree_on_alphabet_from_max_g5_depth_and_upper
      with (word_fuel := word_fuel) (graph_fuel := graph_fuel)
           (max_d := max_d).
    - exact Hdepth.
    - eapply degree_at_most_on_alphabet_from_compression_and_payloads;
        eauto.
  Qed.

  Theorem exact_polynomial_degree_on_alphabet_from_max_g5_depth_and_compression_function :
    forall word_fuel graph_fuel (m : @finite_nfa A)
      (Payload : Type) payloads max_d d c,
      max_g5_red_depth_with_fuel word_fuel graph_fuel m max_d = S d ->
      fnfa_well_formed m ->
      1 <= graph_fuel ->
      NoDup payloads ->
      length payloads <= c ->
      g5_walk_compression_bound word_fuel graph_fuel m (S d) ->
      accepting_run_g5_payload_function_on_alphabet
        word_fuel m Payload payloads (S d) ->
      exact_polynomial_degree_on_alphabet m (S d).
  Proof.
    intros word_fuel graph_fuel m Payload payloads max_d d c
      Hdepth Hwf Hfuel Hnodup Hpayload_bound Hcompress Hpayloads.
    eapply exact_polynomial_degree_on_alphabet_from_max_g5_depth_and_compression;
      eauto.
    now apply accepting_run_g5_payload_injection_from_function.
  Qed.

  Definition no_EDA_g5_occurrence_signature_bound
      (m : @finite_nfa A)
      (Code : Type)
      (d c : nat) : Prop :=
    no_EDA m ->
    accepting_endpoint_occurrence_codes_upper_on_alphabet m Code d c.

  Definition no_EDA_g5_polynomial_signature_bound
      (m : @finite_nfa A)
      (Payload : Type)
      (payloads : list Payload)
      (d c : nat) : Prop :=
    no_EDA m ->
    accepting_endpoint_polynomial_signatures_on_alphabet
      m Payload payloads d c.

  Definition no_EDA_g5_walk_signature_bound
      (word_fuel : nat)
      (m : @finite_nfa A)
      (Payload : Type)
      (payloads : list Payload)
      (d c : nat) : Prop :=
    no_EDA m ->
    accepting_endpoint_g5_walk_signatures_on_alphabet
      word_fuel m Payload payloads d c.

  Definition no_EDA_run_g5_walk_signature_bound
      (word_fuel : nat)
      (m : @finite_nfa A)
      (Payload : Type)
      (payloads : list Payload)
      (d c : nat) : Prop :=
    no_EDA m ->
    accepting_run_g5_walk_signatures_on_alphabet
      word_fuel m Payload payloads d c.

  Definition no_EDA_g5_walk_compression_bound
      (word_fuel graph_fuel : nat)
      (m : @finite_nfa A)
      (d : nat) : Prop :=
    no_EDA m ->
    g5_walk_compression_bound word_fuel graph_fuel m d.

  Definition no_EDA_g5_simple_walk_reduction
      (word_fuel graph_fuel : nat)
      (m : @finite_nfa A)
      (d : nat) : Prop :=
    let components := scc_quotient_with_fuel graph_fuel m in
    no_EDA m ->
    max_g5_red_depth_with_fuel
      word_fuel graph_fuel m (length components) = d ->
    forall walk,
      walk <> [] ->
      Forall (fun c => In c components) walk ->
      g5_walkb word_fuel graph_fuel m walk = true ->
      exists short,
        short <> [] /\
        NoDup short /\
        Forall (fun c => In c components) short /\
        g5_walkb word_fuel graph_fuel m short = true /\
        length short <= length walk.

  Definition no_EDA_g5_bounded_walk_reduction
      (word_fuel graph_fuel : nat)
      (m : @finite_nfa A)
      (d : nat) : Prop :=
    let components := scc_quotient_with_fuel graph_fuel m in
    no_EDA m ->
    max_g5_red_depth_with_fuel
      word_fuel graph_fuel m (length components) = d ->
    g5_bounded_walk_reduction word_fuel graph_fuel m.

  Lemma no_EDA_g5_bounded_walk_reduction_from_simple_compression :
    forall word_fuel graph_fuel (m : @finite_nfa A) d,
      no_EDA_g5_simple_walk_reduction word_fuel graph_fuel m d ->
      no_EDA_g5_bounded_walk_reduction word_fuel graph_fuel m d.
  Proof.
    intros word_fuel graph_fuel m d Hsimple Hno Hmax.
    unfold no_EDA_g5_simple_walk_reduction in Hsimple.
    eapply g5_bounded_walk_reduction_from_simple_compression.
    eapply g5_simple_walk_compression_bound_from_simple_reduction.
    - exact Hmax.
    - rewrite <- Hmax.
      apply max_g5_red_depth_with_fuel_le.
    - exact (Hsimple Hno Hmax).
  Qed.

  Lemma no_EDA_g5_walk_compression_bound_from_simple_reduction :
    forall word_fuel graph_fuel (m : @finite_nfa A) d,
      let components := scc_quotient_with_fuel graph_fuel m in
      max_g5_red_depth_with_fuel
        word_fuel graph_fuel m (length components) = d ->
      no_EDA_g5_simple_walk_reduction word_fuel graph_fuel m d ->
      no_EDA_g5_walk_compression_bound word_fuel graph_fuel m d.
  Proof.
    intros word_fuel graph_fuel m d components Hmax Hreduce Hno.
    unfold no_EDA_g5_simple_walk_reduction in Hreduce.
    eapply g5_walk_compression_bound_from_simple.
    eapply g5_simple_walk_compression_bound_from_simple_reduction.
    - exact Hmax.
    - rewrite <- Hmax.
      apply max_g5_red_depth_with_fuel_le.
    - exact (Hreduce Hno Hmax).
  Qed.

  Lemma no_EDA_g5_walk_compression_bound_from_bounded_reduction :
    forall word_fuel graph_fuel (m : @finite_nfa A) d,
      let components := scc_quotient_with_fuel graph_fuel m in
      max_g5_red_depth_with_fuel
        word_fuel graph_fuel m (length components) = d ->
      d <= length components ->
      no_EDA_g5_bounded_walk_reduction word_fuel graph_fuel m d ->
      no_EDA_g5_walk_compression_bound word_fuel graph_fuel m d.
  Proof.
    intros word_fuel graph_fuel m d components Hmax Hle Hreduce Hno.
    unfold no_EDA_g5_bounded_walk_reduction in Hreduce.
    eapply g5_walk_compression_bound_from_bounded_reduction.
    - exact Hmax.
    - exact Hle.
    - exact (Hreduce Hno Hmax).
  Qed.

  Lemma no_EDA_g5_walk_compression_bound_from_max :
    forall word_fuel graph_fuel (m : @finite_nfa A) d,
      let components := scc_quotient_with_fuel graph_fuel m in
      max_g5_red_depth_with_fuel
        word_fuel graph_fuel m (length components) = d ->
      d <= length components ->
      no_EDA_g5_walk_compression_bound word_fuel graph_fuel m d.
  Proof.
    intros word_fuel graph_fuel m d components Hmax Hle Hno.
    eapply g5_walk_compression_bound_from_simple.
    eapply g5_simple_walk_compression_bound_from_max.
    - exact Hmax.
    - exact Hle.
  Qed.

  Theorem exact_polynomial_degree_on_alphabet_from_no_EDA_g5_signatures :
    forall word_fuel graph_fuel (m : @finite_nfa A) (Code : Type) d c,
      ambiguity_growth_g5_lower_bound_with_fuel word_fuel graph_fuel m =
        GrowthPolynomialLowerBound (S d) ->
      no_EDA m ->
      no_EDA_g5_occurrence_signature_bound m Code (S d) c ->
      exact_polynomial_degree_on_alphabet m (S d).
  Proof.
    intros word_fuel graph_fuel m Code d c Hlower Hno Hsig.
    eapply exact_polynomial_degree_on_alphabet_from_g5_lower_bound_and_occurrence_codes.
    - exact Hlower.
    - now apply Hsig.
  Qed.

  Theorem exact_polynomial_degree_on_alphabet_from_no_EDA_g5_polynomial_signatures :
    forall word_fuel graph_fuel (m : @finite_nfa A)
      (Payload : Type) payloads d c,
      ambiguity_growth_g5_lower_bound_with_fuel word_fuel graph_fuel m =
        GrowthPolynomialLowerBound (S d) ->
      no_EDA m ->
      no_EDA_g5_polynomial_signature_bound m Payload payloads (S d) c ->
      exact_polynomial_degree_on_alphabet m (S d).
  Proof.
    intros word_fuel graph_fuel m Payload payloads d c Hlower Hno Hsig.
    eapply exact_polynomial_degree_on_alphabet_from_g5_lower_bound_and_polynomial_signatures.
    - exact Hlower.
    - now apply Hsig.
  Qed.

  Theorem exact_polynomial_degree_on_alphabet_from_no_EDA_g5_walk_signatures :
    forall word_fuel graph_fuel (m : @finite_nfa A)
      (Payload : Type) payloads d c,
      ambiguity_growth_g5_lower_bound_with_fuel word_fuel graph_fuel m =
        GrowthPolynomialLowerBound (S d) ->
      no_EDA m ->
      no_EDA_g5_walk_signature_bound
        word_fuel m Payload payloads (S d) c ->
      exact_polynomial_degree_on_alphabet m (S d).
  Proof.
    intros word_fuel graph_fuel m Payload payloads d c Hlower Hno Hsig.
    eapply exact_polynomial_degree_on_alphabet_from_g5_lower_bound_and_g5_walk_signatures.
    - exact Hlower.
    - now apply Hsig.
  Qed.

  Theorem exact_polynomial_degree_on_alphabet_from_no_EDA_run_g5_walk_signatures :
    forall word_fuel graph_fuel (m : @finite_nfa A)
      (Payload : Type) payloads d c,
      ambiguity_growth_g5_lower_bound_with_fuel word_fuel graph_fuel m =
        GrowthPolynomialLowerBound (S d) ->
      no_EDA m ->
      no_EDA_run_g5_walk_signature_bound
        word_fuel m Payload payloads (S d) c ->
      exact_polynomial_degree_on_alphabet m (S d).
  Proof.
    intros word_fuel graph_fuel m Payload payloads d c Hlower Hno Hsig.
    eapply exact_polynomial_degree_on_alphabet_from_g5_lower_bound_and_run_g5_walk_signatures.
    - exact Hlower.
    - now apply Hsig.
  Qed.

  Theorem exact_polynomial_degree_on_alphabet_from_no_EDA_compression :
    forall word_fuel graph_fuel (m : @finite_nfa A)
      (Payload : Type) payloads max_d d c,
      max_g5_red_depth_with_fuel word_fuel graph_fuel m max_d = S d ->
      no_EDA m ->
      fnfa_well_formed m ->
      1 <= graph_fuel ->
      NoDup payloads ->
      length payloads <= c ->
      no_EDA_g5_walk_compression_bound
        word_fuel graph_fuel m (S d) ->
      accepting_run_g5_payload_injection_on_alphabet
        word_fuel m Payload payloads (S d) ->
      exact_polynomial_degree_on_alphabet m (S d).
  Proof.
    intros word_fuel graph_fuel m Payload payloads max_d d c
      Hdepth Hno Hwf Hfuel Hnodup Hpayload_bound Hcompress Hpayloads.
    eapply exact_polynomial_degree_on_alphabet_from_max_g5_depth_and_compression.
    - exact Hdepth.
    - exact Hwf.
    - exact Hfuel.
    - exact Hnodup.
    - exact Hpayload_bound.
    - now apply Hcompress.
    - exact Hpayloads.
  Qed.

  Theorem exact_polynomial_degree_on_alphabet_from_no_EDA_compression_function :
    forall word_fuel graph_fuel (m : @finite_nfa A)
      (Payload : Type) payloads max_d d c,
      max_g5_red_depth_with_fuel word_fuel graph_fuel m max_d = S d ->
      no_EDA m ->
      fnfa_well_formed m ->
      1 <= graph_fuel ->
      NoDup payloads ->
      length payloads <= c ->
      no_EDA_g5_walk_compression_bound
        word_fuel graph_fuel m (S d) ->
      accepting_run_g5_payload_function_on_alphabet
        word_fuel m Payload payloads (S d) ->
      exact_polynomial_degree_on_alphabet m (S d).
  Proof.
    intros word_fuel graph_fuel m Payload payloads max_d d c
      Hdepth Hno Hwf Hfuel Hnodup Hpayload_bound Hcompress Hpayloads.
    eapply exact_polynomial_degree_on_alphabet_from_no_EDA_compression.
    - exact Hdepth.
    - exact Hno.
    - exact Hwf.
    - exact Hfuel.
    - exact Hnodup.
    - exact Hpayload_bound.
    - exact Hcompress.
    - now apply accepting_run_g5_payload_injection_from_function.
  Qed.

  Theorem exact_polynomial_degree_on_alphabet_from_no_EDA_payload_function :
    forall word_fuel graph_fuel (m : @finite_nfa A)
      (Payload : Type) payloads d c,
      let components := scc_quotient_with_fuel graph_fuel m in
      max_g5_red_depth_with_fuel
        word_fuel graph_fuel m (length components) = S d ->
      no_EDA m ->
      fnfa_well_formed m ->
      1 <= graph_fuel ->
      NoDup payloads ->
      length payloads <= c ->
      accepting_run_g5_payload_function_on_alphabet
        word_fuel m Payload payloads (S d) ->
      exact_polynomial_degree_on_alphabet m (S d).
  Proof.
    intros word_fuel graph_fuel m Payload payloads d c components
      Hmax Hno Hwf Hfuel Hnodup Hpayload_bound Hpayloads.
    eapply exact_polynomial_degree_on_alphabet_from_no_EDA_compression_function.
    - exact Hmax.
    - exact Hno.
    - exact Hwf.
    - exact Hfuel.
    - exact Hnodup.
    - exact Hpayload_bound.
    - eapply no_EDA_g5_walk_compression_bound_from_max.
      + exact Hmax.
      + rewrite <- Hmax.
        apply max_g5_red_depth_with_fuel_le.
    - exact Hpayloads.
  Qed.

  Theorem exact_polynomial_degree_on_alphabet_from_no_EDA_boundary_indices :
    forall word_fuel graph_fuel (m : @finite_nfa A) d,
      let components := scc_quotient_with_fuel graph_fuel m in
      max_g5_red_depth_with_fuel
        word_fuel graph_fuel m (length components) = S d ->
      no_EDA m ->
      fnfa_well_formed m ->
      1 <= graph_fuel ->
      accepting_run_g5_boundary_index_payload_function_on_alphabet
        word_fuel m (S d) ->
      exact_polynomial_degree_on_alphabet m (S d).
  Proof.
    intros word_fuel graph_fuel m d components Hmax Hno Hwf Hfuel Hpayloads.
    eapply exact_polynomial_degree_on_alphabet_from_no_EDA_payload_function
      with
        (Payload := list nat)
        (payloads :=
          nat_vectors_below (S (S d)) (state_pair_payload_bound m))
        (c := Nat.pow (state_pair_payload_bound m) (S (S d))).
    - exact Hmax.
    - exact Hno.
    - exact Hwf.
    - exact Hfuel.
    - apply nat_vectors_below_NoDup.
    - rewrite nat_vectors_below_length. lia.
    - now apply accepting_run_g5_payload_function_from_boundary_indices.
  Qed.

  Theorem exact_polynomial_degree_on_alphabet_from_no_EDA_positive_boundary_indices :
    forall word_fuel graph_fuel (m : @finite_nfa A) d,
      let components := scc_quotient_with_fuel graph_fuel m in
      max_g5_red_depth_with_fuel
        word_fuel graph_fuel m (length components) = S d ->
      no_EDA m ->
      fnfa_well_formed m ->
      1 <= graph_fuel ->
      accepting_run_g5_positive_boundary_index_payload_function_on_alphabet
        word_fuel m (S d) ->
      exact_polynomial_degree_on_alphabet m (S d).
  Proof.
    intros word_fuel graph_fuel m d components Hmax Hno Hwf Hfuel Hpayloads.
    eapply exact_polynomial_degree_on_alphabet_from_no_EDA_payload_function
      with
        (Payload := list nat)
        (payloads :=
          nat_vectors_below (S (S d)) (S (state_pair_payload_bound m)))
        (c := Nat.pow (S (state_pair_payload_bound m)) (S (S d))).
    - exact Hmax.
    - exact Hno.
    - exact Hwf.
    - exact Hfuel.
    - apply nat_vectors_below_NoDup.
    - rewrite nat_vectors_below_length. lia.
    - now apply accepting_run_g5_payload_function_from_positive_boundary_indices.
  Qed.

  Theorem exact_polynomial_degree_on_alphabet_from_no_EDA_boundary_pairs :
    forall word_fuel graph_fuel (m : @finite_nfa A) d,
      let components := scc_quotient_with_fuel graph_fuel m in
      max_g5_red_depth_with_fuel
        word_fuel graph_fuel m (length components) = S d ->
      no_EDA m ->
      fnfa_well_formed m ->
      1 <= graph_fuel ->
      accepting_run_g5_boundary_pair_payload_function_on_alphabet
        word_fuel m (S d) ->
      exact_polynomial_degree_on_alphabet m (S d).
  Proof.
    intros word_fuel graph_fuel m d components Hmax Hno Hwf Hfuel Hpayloads.
    eapply exact_polynomial_degree_on_alphabet_from_no_EDA_boundary_indices.
    - exact Hmax.
    - exact Hno.
    - exact Hwf.
    - exact Hfuel.
    - now apply accepting_run_g5_boundary_indices_from_pair_payloads.
  Qed.

  Theorem exact_polynomial_degree_on_alphabet_from_no_EDA_trace_collision_to_EDA :
    forall word_fuel graph_fuel (m : @finite_nfa A) d,
      let components := scc_quotient_with_fuel graph_fuel m in
      max_g5_red_depth_with_fuel
        word_fuel graph_fuel m (length components) = S d ->
      no_EDA m ->
      fnfa_well_formed m ->
      1 <= graph_fuel ->
      trace_boundary_payload_collisions_imply_EDA_on_alphabet
        word_fuel m (S d) ->
      exact_polynomial_degree_on_alphabet m (S d).
  Proof.
    intros word_fuel graph_fuel m d components
      Hmax Hno Hwf Hfuel Hcollision_to_eda.
    eapply exact_polynomial_degree_on_alphabet_from_no_EDA_boundary_pairs.
    - exact Hmax.
    - exact Hno.
    - exact Hwf.
    - exact Hfuel.
    - eapply accepting_run_g5_boundary_pairs_from_trace_separator.
      + exact Hwf.
      + eapply trace_boundary_payload_separator_from_no_EDA.
        * exact Hno.
        * exact Hcollision_to_eda.
  Qed.

  Theorem exact_polynomial_degree_on_alphabet_from_no_EDA_positive_trace_collision_to_EDA :
    forall word_fuel graph_fuel (m : @finite_nfa A) d,
      let components := scc_quotient_with_fuel graph_fuel m in
      max_g5_red_depth_with_fuel
        word_fuel graph_fuel m (length components) = S d ->
      no_EDA m ->
      fnfa_well_formed m ->
      1 <= graph_fuel ->
      trace_boundary_positive_payload_collisions_imply_EDA_on_alphabet
        word_fuel m (S d) ->
      exact_polynomial_degree_on_alphabet m (S d).
  Proof.
    intros word_fuel graph_fuel m d components
      Hmax Hno Hwf Hfuel Hcollision_to_eda.
    eapply exact_polynomial_degree_on_alphabet_from_no_EDA_positive_boundary_indices.
    - exact Hmax.
    - exact Hno.
    - exact Hwf.
    - exact Hfuel.
    - eapply accepting_run_g5_positive_boundary_indices_from_trace_separator.
      + exact Hwf.
      + eapply trace_boundary_positive_payload_separator_from_no_EDA.
        * exact Hno.
        * exact Hcollision_to_eda.
  Qed.

  Theorem exact_polynomial_degree_on_alphabet_from_no_EDA_trace_payload_list_collision_to_EDA :
    forall word_fuel graph_fuel (m : @finite_nfa A) d,
      let components := scc_quotient_with_fuel graph_fuel m in
      max_g5_red_depth_with_fuel
        word_fuel graph_fuel m (length components) = S d ->
      no_EDA m ->
      fnfa_well_formed m ->
      1 <= graph_fuel ->
      trace_boundary_payload_list_collisions_imply_EDA_on_alphabet
        word_fuel m (S d) ->
      exact_polynomial_degree_on_alphabet m (S d).
  Proof.
    intros word_fuel graph_fuel m d components
      Hmax Hno Hwf Hfuel Hcollision_to_eda.
    eapply exact_polynomial_degree_on_alphabet_from_no_EDA_positive_trace_collision_to_EDA.
    - exact Hmax.
    - exact Hno.
    - exact Hwf.
    - exact Hfuel.
    - now apply trace_boundary_positive_collisions_imply_EDA_from_list_collisions.
  Qed.

  Theorem exact_polynomial_degree_on_alphabet_from_no_EDA_compression_endpoint_pairs :
    forall word_fuel graph_fuel (m : @finite_nfa A) max_d d,
      max_g5_red_depth_with_fuel word_fuel graph_fuel m max_d = S d ->
      no_EDA m ->
      fnfa_well_formed m ->
      1 <= graph_fuel ->
      no_EDA_g5_walk_compression_bound
        word_fuel graph_fuel m (S d) ->
      accepting_run_g5_endpoint_pair_separates_on_alphabet
        word_fuel m (S d) ->
      exact_polynomial_degree_on_alphabet m (S d).
  Proof.
    intros word_fuel graph_fuel m max_d d
      Hdepth Hno Hwf Hfuel Hcompress Hseparate.
    eapply exact_polynomial_degree_on_alphabet_from_no_EDA_compression_function
      with
        (Payload := option (finite_state m * finite_state m))
        (payloads := optional_finite_state_pair_payloads m)
        (c := S (length (fnfa_states m) * length (fnfa_states m))).
    - exact Hdepth.
    - exact Hno.
    - exact Hwf.
    - exact Hfuel.
    - apply optional_finite_state_pair_payloads_NoDup.
    - apply optional_finite_state_pair_payloads_length_le.
    - exact Hcompress.
    - now apply accepting_run_g5_payload_function_from_endpoint_pairs.
  Qed.

  Theorem exact_polynomial_degree_on_alphabet_from_no_EDA_simple_reduction_endpoint_pairs :
    forall word_fuel graph_fuel (m : @finite_nfa A) d,
      let components := scc_quotient_with_fuel graph_fuel m in
      max_g5_red_depth_with_fuel
        word_fuel graph_fuel m (length components) = S d ->
      no_EDA m ->
      fnfa_well_formed m ->
      1 <= graph_fuel ->
      no_EDA_g5_simple_walk_reduction
        word_fuel graph_fuel m (S d) ->
      accepting_run_g5_endpoint_pair_separates_on_alphabet
        word_fuel m (S d) ->
      exact_polynomial_degree_on_alphabet m (S d).
  Proof.
    intros word_fuel graph_fuel m d components
      Hmax Hno Hwf Hfuel Hsimple Hseparate.
    eapply exact_polynomial_degree_on_alphabet_from_no_EDA_compression_endpoint_pairs.
    - exact Hmax.
    - exact Hno.
    - exact Hwf.
    - exact Hfuel.
    - eapply no_EDA_g5_walk_compression_bound_from_simple_reduction.
      + exact Hmax.
      + exact Hsimple.
    - exact Hseparate.
  Qed.

  Theorem exact_polynomial_degree_on_alphabet_from_no_EDA_bounded_reduction_endpoint_pairs :
    forall word_fuel graph_fuel (m : @finite_nfa A) d,
      let components := scc_quotient_with_fuel graph_fuel m in
      max_g5_red_depth_with_fuel
        word_fuel graph_fuel m (length components) = S d ->
      no_EDA m ->
      fnfa_well_formed m ->
      1 <= graph_fuel ->
      no_EDA_g5_bounded_walk_reduction
        word_fuel graph_fuel m (S d) ->
      accepting_run_g5_endpoint_pair_separates_on_alphabet
        word_fuel m (S d) ->
      exact_polynomial_degree_on_alphabet m (S d).
  Proof.
    intros word_fuel graph_fuel m d components
      Hmax Hno Hwf Hfuel Hbounded Hseparate.
    eapply exact_polynomial_degree_on_alphabet_from_no_EDA_compression_endpoint_pairs.
    - exact Hmax.
    - exact Hno.
    - exact Hwf.
    - exact Hfuel.
    - eapply no_EDA_g5_walk_compression_bound_from_bounded_reduction.
      + exact Hmax.
      + rewrite <- Hmax.
        apply max_g5_red_depth_with_fuel_le.
      + exact Hbounded.
    - exact Hseparate.
  Qed.

  Theorem exact_polynomial_degree_on_alphabet_from_no_EDA_endpoint_pairs :
    forall word_fuel graph_fuel (m : @finite_nfa A) d,
      let components := scc_quotient_with_fuel graph_fuel m in
      max_g5_red_depth_with_fuel
        word_fuel graph_fuel m (length components) = S d ->
      no_EDA m ->
      fnfa_well_formed m ->
      1 <= graph_fuel ->
      accepting_run_g5_endpoint_pair_separates_on_alphabet
        word_fuel m (S d) ->
      exact_polynomial_degree_on_alphabet m (S d).
  Proof.
    intros word_fuel graph_fuel m d components Hmax Hno Hwf Hfuel Hseparate.
    eapply exact_polynomial_degree_on_alphabet_from_no_EDA_compression_endpoint_pairs.
    - exact Hmax.
    - exact Hno.
    - exact Hwf.
    - exact Hfuel.
    - eapply no_EDA_g5_walk_compression_bound_from_max.
      + exact Hmax.
      + rewrite <- Hmax.
        apply max_g5_red_depth_with_fuel_le.
    - exact Hseparate.
  Qed.

  Theorem ambiguity_growth_g5_lower_bound_with_fuel_sound_exponential_or_unbounded :
    forall word_fuel graph_fuel (m : @finite_nfa A),
      ambiguity_growth_g5_lower_bound_with_fuel word_fuel graph_fuel m =
        GrowthExponential ->
      exponentially_ambiguous (fnfa_base m) \/
      (forall d, degree_at_least (fnfa_base m) (S d)).
  Proof.
    intros word_fuel graph_fuel m H.
    unfold ambiguity_growth_g5_lower_bound_with_fuel in H.
    set (components := scc_quotient_with_fuel graph_fuel m) in H.
    destruct (edab_with_fuel word_fuel m) eqn:Heda.
    - left.
      now apply edab_with_fuel_exponentially_ambiguous with (fuel := word_fuel).
    - simpl in H.
      destruct (g5_has_red_self_loopb word_fuel graph_fuel m) eqn:Hloop.
      + right.
        intros d.
        now apply g5_has_red_self_loopb_degree_at_least
          with (word_fuel := word_fuel) (graph_fuel := graph_fuel).
      + discriminate.
  Qed.

  Theorem ambiguity_growth_g5_lower_bound_with_fuel_sound_exponential :
    forall word_fuel graph_fuel (m : @finite_nfa A),
      ambiguity_growth_g5_lower_bound_with_fuel word_fuel graph_fuel m =
        GrowthExponential ->
      exponentially_ambiguous (fnfa_base m).
  Proof.
    intros word_fuel graph_fuel m H.
    unfold ambiguity_growth_g5_lower_bound_with_fuel in H.
    set (components := scc_quotient_with_fuel graph_fuel m) in H.
    destruct (edab_with_fuel word_fuel m) eqn:Heda.
    - now apply edab_with_fuel_exponentially_ambiguous with (fuel := word_fuel).
    - simpl in H.
      destruct (g5_has_red_self_loopb word_fuel graph_fuel m) eqn:Hloop.
      + now apply g5_has_red_self_loopb_exponentially_ambiguous
          with (word_fuel := word_fuel) (graph_fuel := graph_fuel).
      + discriminate.
  Qed.

  Lemma max_ida_depth_with_fuel_sound_positive :
    forall fuel (m : @finite_nfa A) max_d d,
      max_ida_depth_with_fuel fuel m max_d = S d ->
      degree_at_least (fnfa_base m) (S d).
  Proof.
    intros fuel m max_d.
    induction max_d as [| max_d IH]; intros d Hmax.
    - simpl in Hmax. discriminate.
    - change
        ((if idab_d_with_fuel fuel m (S max_d)
          then S max_d
          else max_ida_depth_with_fuel fuel m max_d) = S d) in Hmax.
      destruct (idab_d_with_fuel fuel m (S max_d)) eqn:Hhit.
      + inversion Hmax; subst.
        now apply idab_d_with_fuel_degree_at_least with (fuel := fuel).
      + now apply IH.
  Qed.

  Lemma max_ida_depth_graph_with_fuel_sound_positive :
    forall word_fuel graph_fuel (m : @finite_nfa A) max_d d,
      max_ida_depth_graph_with_fuel word_fuel graph_fuel m max_d = S d ->
      degree_at_least (fnfa_base m) (S d).
  Proof.
    intros word_fuel graph_fuel m max_d.
    induction max_d as [| max_d IH]; intros d Hmax.
    - simpl in Hmax. discriminate.
    - change
        ((if idab_d_graph_with_fuel word_fuel graph_fuel m (S max_d)
          then S max_d
          else max_ida_depth_graph_with_fuel word_fuel graph_fuel m max_d)
          = S d) in Hmax.
      destruct (idab_d_graph_with_fuel word_fuel graph_fuel m (S max_d))
        eqn:Hhit.
      + inversion Hmax; subst.
        now apply idab_d_graph_with_fuel_degree_at_least
          with (word_fuel := word_fuel) (graph_fuel := graph_fuel).
      + now apply IH.
  Qed.

  Theorem ambiguity_growth_lower_bound_with_fuel_sound_exponential :
    forall fuel (m : @finite_nfa A) max_d,
      ambiguity_growth_lower_bound_with_fuel fuel m max_d =
        GrowthExponential ->
      exponentially_ambiguous (fnfa_base m).
  Proof.
    intros fuel m max_d H.
    unfold ambiguity_growth_lower_bound_with_fuel in H.
    destruct (edab_with_fuel fuel m) eqn:Heda; try discriminate.
    now apply edab_with_fuel_exponentially_ambiguous with (fuel := fuel).
  Qed.

  Theorem ambiguity_growth_lower_bound_with_fuel_sound_polynomial :
    forall fuel (m : @finite_nfa A) max_d d,
      ambiguity_growth_lower_bound_with_fuel fuel m max_d =
        GrowthPolynomialLowerBound (S d) ->
      degree_at_least (fnfa_base m) (S d).
  Proof.
    intros fuel m max_d d H.
    unfold ambiguity_growth_lower_bound_with_fuel in H.
    destruct (edab_with_fuel fuel m); try discriminate.
    inversion H; subst.
    rewrite H1.
    apply (max_ida_depth_with_fuel_sound_positive fuel m max_d d).
    assumption.
  Qed.

  Theorem ambiguity_growth_lower_bound_graph_with_fuel_sound_exponential :
    forall word_fuel graph_fuel (m : @finite_nfa A) max_d,
      ambiguity_growth_lower_bound_graph_with_fuel
        word_fuel graph_fuel m max_d = GrowthExponential ->
      exponentially_ambiguous (fnfa_base m).
  Proof.
    intros word_fuel graph_fuel m max_d H.
    unfold ambiguity_growth_lower_bound_graph_with_fuel in H.
    destruct (edab_with_fuel word_fuel m) eqn:Heda; try discriminate.
    now apply edab_with_fuel_exponentially_ambiguous with (fuel := word_fuel).
  Qed.

  Theorem ambiguity_growth_lower_bound_graph_with_fuel_sound_polynomial :
    forall word_fuel graph_fuel (m : @finite_nfa A) max_d d,
      ambiguity_growth_lower_bound_graph_with_fuel
        word_fuel graph_fuel m max_d =
        GrowthPolynomialLowerBound (S d) ->
      degree_at_least (fnfa_base m) (S d).
  Proof.
    intros word_fuel graph_fuel m max_d d H.
    unfold ambiguity_growth_lower_bound_graph_with_fuel in H.
    destruct (edab_with_fuel word_fuel m); try discriminate.
    inversion H; subst.
    rewrite H1.
    apply (max_ida_depth_graph_with_fuel_sound_positive
      word_fuel graph_fuel m max_d d).
    assumption.
  Qed.
End InfiniteAmbiguity.
