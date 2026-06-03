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

Lemma sum_nats_In_le :
  forall xs x,
    In x xs ->
    x <= sum_nats xs.
Proof.
  induction xs as [| y ys IH]; simpl; intros x Hin.
  - contradiction.
  - destruct Hin as [Heq | Hin].
    + subst. lia.
    + specialize (IH x Hin). lia.
Qed.

Lemma sum_map_In_le :
  forall {B : Type} (f : B -> nat) xs x,
    In x xs ->
    f x <= sum_nats (map f xs).
Proof.
  intros B f xs x Hin.
  apply sum_nats_In_le.
  now apply in_map.
Qed.

Lemma sum_map_ge_two_cases :
  forall {B : Type} (f : B -> nat) xs,
    NoDup xs ->
    2 <= sum_nats (map f xs) ->
    (exists x, In x xs /\ 2 <= f x) \/
    (exists x y,
      In x xs /\ In y xs /\ x <> y /\ 0 < f x /\ 0 < f y).
Proof.
  intros B f xs.
  induction xs as [| x xs IH]; simpl; intros Hnodup Hsum.
  - lia.
  - inversion Hnodup as [| z zs Hnotin Hnodup']; subst.
    destruct (f x) as [| n] eqn:Hfx.
    + assert (Htail : 2 <= sum_nats (map f xs)) by lia.
      destruct (IH Hnodup' Htail) as
        [[y [Hy Hfy]] | [y [z [Hy [Hz [Hneq [Hfy Hfz]]]]]]].
      * left. exists y. split; simpl; auto.
      * right. exists y, z. repeat split; simpl; auto.
    + destruct n as [| n].
      * right.
        assert (Htail_pos : 0 < sum_nats (map f xs)) by lia.
        apply sum_map_pos_In in Htail_pos as [y [Hy Hfy]].
        exists x, y.
        repeat split; simpl; auto.
        -- intros Heq. subst. contradiction.
        -- rewrite Hfx. lia.
      * left. exists x. split; simpl; auto. rewrite Hfx. lia.
Qed.

Lemma sum_map_mul_le :
  forall {B : Type} (f g : B -> nat) c xs,
    (forall x, In x xs -> f x * c <= g x) ->
    sum_nats (map f xs) * c <= sum_nats (map g xs).
Proof.
  intros B f g c xs H.
  induction xs as [| x xs IH]; simpl.
  - lia.
  - rewrite Nat.mul_add_distr_r.
    assert (Hx : f x * c <= g x).
    { apply H. simpl. auto. }
    assert (Hxs : sum_nats (map f xs) * c <= sum_nats (map g xs)).
    { apply IH. intros y Hy. apply H. simpl. auto. }
    lia.
Qed.

Lemma sum_map_two_mul_le :
  forall {B : Type} (f1 f2 g : B -> nat) c1 c2 xs,
    (forall x, In x xs -> f1 x * c1 + f2 x * c2 <= g x) ->
    sum_nats (map f1 xs) * c1 + sum_nats (map f2 xs) * c2 <=
      sum_nats (map g xs).
Proof.
  intros B f1 f2 g c1 c2 xs H.
  induction xs as [| x xs IH]; simpl.
  - lia.
  - rewrite !Nat.mul_add_distr_r.
    assert (Hx : f1 x * c1 + f2 x * c2 <= g x).
    { apply H. simpl. auto. }
    assert (Hxs :
      sum_nats (map f1 xs) * c1 + sum_nats (map f2 xs) * c2 <=
        sum_nats (map g xs)).
    { apply IH. intros y Hy. apply H. simpl. auto. }
    lia.
Qed.

Lemma nat_le_mul_with_positive :
  forall a b x,
    1 <= a ->
    1 <= b ->
    x <= a * x * b.
Proof.
  intros a b x Ha Hb.
  assert (Hax : x <= a * x).
  {
    rewrite <- (Nat.mul_1_l x) at 1.
    apply Nat.mul_le_mono_r. exact Ha.
  }
  assert (Hab : a * x <= a * x * b).
  {
    rewrite <- (Nat.mul_1_r (a * x)) at 1.
    apply Nat.mul_le_mono_l. exact Hb.
  }
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

  Record finite_nfa_wf (m : finite_nfa) : Prop := {
    fnfa_states_nodup :
      NoDup (fnfa_states m);
    fnfa_starts_in_states :
      forall q,
        In q (nfa_start (fnfa_base m)) ->
        In q (fnfa_states m);
    fnfa_steps_in_states :
      forall q a q',
        In q (fnfa_states m) ->
        In q' (nfa_step (fnfa_base m) q a) ->
        In q' (fnfa_states m);
    fnfa_steps_in_alphabet :
      forall q a q',
        In q (fnfa_states m) ->
        In q' (nfa_step (fnfa_base m) q a) ->
        In a (fnfa_alphabet m);
    fnfa_step_targets_nodup :
      forall q a,
        In q (fnfa_states m) ->
        NoDup (nfa_step (fnfa_base m) q a)
  }.

  Definition fnfa_state_inb
      (m : finite_nfa)
      (q : nfa_state (fnfa_base m)) : bool :=
    existsb (fnfa_state_eqb m q) (fnfa_states m).

  Lemma fnfa_state_inb_sound :
    forall (m : finite_nfa) q,
      fnfa_state_inb m q = true ->
      In q (fnfa_states m).
  Proof.
    intros m q H.
    unfold fnfa_state_inb in H.
    apply existsb_exists in H as [q' [Hin Heq]].
    apply fnfa_state_eqb_sound in Heq.
    now subst.
  Qed.

  Lemma fnfa_state_inb_complete :
    forall (m : finite_nfa) q,
      In q (fnfa_states m) ->
      fnfa_state_inb m q = true.
  Proof.
    intros m q Hin.
    unfold fnfa_state_inb.
    apply existsb_exists.
    exists q. split; auto.
    apply fnfa_state_eqb_complete. reflexivity.
  Qed.

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

  Fixpoint word_power (w : list A) (n : nat) : list A :=
    match n with
    | O => []
    | S n' => w ++ word_power w n'
    end.

  Lemma path_from_app :
    forall (m : nfa) p u q v r,
      path_from m p u q ->
      path_from m q v r ->
      path_from m p (u ++ v) r.
  Proof.
    intros m p u q v r Hleft Hright.
    induction Hleft; simpl; auto.
    eapply Path_cons; eauto.
  Qed.

  Lemma finite_nfa_wf_start_in_states :
    forall (m : finite_nfa) q,
      finite_nfa_wf m ->
      In q (nfa_start (fnfa_base m)) ->
      In q (fnfa_states m).
  Proof.
    intros m q Hwf Hstart.
    destruct Hwf as [_ Hstarts _ _ _].
    now apply Hstarts.
  Qed.

  Lemma finite_nfa_wf_step_in_states :
    forall (m : finite_nfa) q a q',
      finite_nfa_wf m ->
      In q (fnfa_states m) ->
      In q' (nfa_step (fnfa_base m) q a) ->
      In q' (fnfa_states m).
  Proof.
    intros m q a q' Hwf Hq Hstep.
    destruct Hwf as [_ _ Hsteps _ _].
    eapply Hsteps; eauto.
  Qed.

  Lemma finite_nfa_wf_step_in_alphabet :
    forall (m : finite_nfa) q a q',
      finite_nfa_wf m ->
      In q (fnfa_states m) ->
      In q' (nfa_step (fnfa_base m) q a) ->
      In a (fnfa_alphabet m).
  Proof.
    intros m q a q' Hwf Hq Hstep.
    destruct Hwf as [_ _ _ Halphabet _].
    eapply Halphabet; eauto.
  Qed.

  Lemma finite_nfa_wf_step_targets_NoDup :
    forall (m : finite_nfa) q a,
      finite_nfa_wf m ->
      In q (fnfa_states m) ->
      NoDup (nfa_step (fnfa_base m) q a).
  Proof.
    intros m q a Hwf Hq.
    destruct Hwf as [_ _ _ _ Hnodup].
    now apply Hnodup.
  Qed.

  Lemma finite_nfa_wf_path_end_in_states :
    forall (m : finite_nfa) p w q,
      finite_nfa_wf m ->
      In p (fnfa_states m) ->
      path_from (fnfa_base m) p w q ->
      In q (fnfa_states m).
  Proof.
    intros m p w q Hwf Hpin Hpath.
    induction Hpath as [q| q a q' w q'' Hstep _ IH].
    - exact Hpin.
    - apply IH.
      eapply finite_nfa_wf_step_in_states; eauto.
  Qed.

  Lemma finite_nfa_wf_path_symbols_in_alphabet :
    forall (m : finite_nfa) p w q,
      finite_nfa_wf m ->
      In p (fnfa_states m) ->
      path_from (fnfa_base m) p w q ->
      Forall (fun a => In a (fnfa_alphabet m)) w.
  Proof.
    intros m p w q Hwf Hpin Hpath.
    induction Hpath as [q| q a q' w q'' Hstep _ IH].
    - constructor.
    - constructor.
      + eapply finite_nfa_wf_step_in_alphabet; eauto.
      + apply IH.
        eapply finite_nfa_wf_step_in_states; eauto.
  Qed.

  Lemma finite_nfa_wf_useful_in_states :
    forall (m : finite_nfa) q,
      finite_nfa_wf m ->
      useful_state (fnfa_base m) q ->
      In q (fnfa_states m).
  Proof.
    intros m q Hwf Huseful.
    destruct Huseful as [q0 [qf [w1 [w2
      [Hstart [Hpath_in [_ Hfinal]]]]]]].
    eapply finite_nfa_wf_path_end_in_states; eauto.
    eapply finite_nfa_wf_start_in_states; eauto.
  Qed.

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

  Lemma fnfa_state_eqb_neq_false :
    forall (m : finite_nfa) x y,
      x <> y ->
      fnfa_state_eqb m x y = false.
  Proof.
    intros m x y Hneq.
    destruct (fnfa_state_eqb m x y) eqn:Heq; auto.
    apply fnfa_state_eqb_sound in Heq.
    contradiction.
  Qed.

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

  Lemma path_runs_between_positive :
    forall (m : finite_nfa) q w r,
      path_from (fnfa_base m) q w r ->
      0 < runs_between m q w r.
  Proof.
    intros m q w r Hpath.
    induction Hpath as [q| q a q' w q'' Hstep _ IH]; simpl.
    - rewrite (fnfa_state_eqb_complete m q q eq_refl). lia.
    - pose proof
        (sum_map_In_le
           (fun s => runs_between m s w q'')
           (nfa_step (fnfa_base m) q a)
           q'
           Hstep) as Hle.
      lia.
  Qed.

  Lemma path_start_runs_to_positive :
    forall (m : finite_nfa) w q q0,
      In q0 (nfa_start (fnfa_base m)) ->
      path_from (fnfa_base m) q0 w q ->
      0 < start_runs_to m w q.
  Proof.
    intros m w q q0 Hstart Hpath.
    unfold start_runs_to.
    pose proof
      (sum_map_In_le
         (fun s => runs_between m s w q)
         (nfa_start (fnfa_base m))
         q0
         Hstart) as Hle.
    pose proof (path_runs_between_positive m q0 w q Hpath) as Hpos.
    lia.
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

  Lemma path_accepting_runs_from_positive :
    forall (m : nfa) q w qf,
      path_from m q w qf ->
      nfa_final m qf = true ->
      0 < accepting_runs_from m q w.
  Proof.
    intros m q w qf Hpath Hfinal.
    induction Hpath as [q| q a q' w q'' Hstep _ IH]; simpl.
    - rewrite Hfinal. lia.
    - pose proof
        (sum_map_In_le
           (fun s => accepting_runs_from m s w)
           (nfa_step m q a)
           q'
           Hstep) as Hle.
      specialize (IH Hfinal).
      lia.
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

  Lemma useful_state_positive_tests :
    forall (m : finite_nfa) q,
      useful_state (fnfa_base m) q ->
      exists w_in w_out,
        0 < start_runs_to m w_in q /\
        0 < accepting_runs_from (fnfa_base m) q w_out.
  Proof.
    intros m q Huseful.
    unfold useful_state in Huseful.
    destruct Huseful as [q0 [qf [w_in [w_out
      [Hstart [Hpath_in [Hpath_out Hfinal]]]]]]].
    exists w_in, w_out.
    split.
    - eapply path_start_runs_to_positive; eauto.
    - eapply path_accepting_runs_from_positive; eauto.
  Qed.

  Lemma runs_between_app_lower :
    forall (m : finite_nfa) p u q v r,
      runs_between m p u q * runs_between m q v r <=
      runs_between m p (u ++ v) r.
  Proof.
    intros m p u.
    revert p.
    induction u as [| a u IH]; intros p q v r; simpl.
    - destruct (fnfa_state_eqb m p q) eqn:Heq.
      + apply fnfa_state_eqb_sound in Heq. subst. lia.
      + lia.
    - apply sum_map_mul_le.
      intros p' _.
      apply IH.
  Qed.

  Lemma runs_between_app_lower_two :
    forall (m : finite_nfa) p q r u v s,
      p <> q ->
      runs_between m r u p * runs_between m p v s +
      runs_between m r u q * runs_between m q v s <=
      runs_between m r (u ++ v) s.
  Proof.
    intros m p q r u.
    revert r.
    induction u as [| a u IH]; intros r v s Hneq; simpl.
    - destruct (fnfa_state_eqb m r p) eqn:Hrp;
        destruct (fnfa_state_eqb m r q) eqn:Hrq.
      + apply fnfa_state_eqb_sound in Hrp.
        apply fnfa_state_eqb_sound in Hrq.
        subst. contradiction.
      + apply fnfa_state_eqb_sound in Hrp. subst. lia.
      + apply fnfa_state_eqb_sound in Hrq. subst. lia.
      + lia.
    - apply sum_map_two_mul_le.
      intros r' _.
      apply IH. exact Hneq.
  Qed.

  Lemma accepting_runs_from_app_lower :
    forall (m : finite_nfa) q v r w,
      runs_between m q v r * accepting_runs_from (fnfa_base m) r w <=
      accepting_runs_from (fnfa_base m) q (v ++ w).
  Proof.
    intros m q v.
    revert q.
    induction v as [| a v IH]; intros q r w; simpl.
    - destruct (fnfa_state_eqb m q r) eqn:Heq.
      + apply fnfa_state_eqb_sound in Heq. subst. lia.
      + lia.
    - apply sum_map_mul_le.
      intros q' _.
      apply IH.
  Qed.

  Lemma accepting_runs_from_app_lower_two :
    forall (m : finite_nfa) p q r v w,
      p <> q ->
      runs_between m r v p * accepting_runs_from (fnfa_base m) p w +
      runs_between m r v q * accepting_runs_from (fnfa_base m) q w <=
      accepting_runs_from (fnfa_base m) r (v ++ w).
  Proof.
    intros m p q r v.
    revert r.
    induction v as [| a v IH]; intros r w Hneq; simpl.
    - destruct (fnfa_state_eqb m r p) eqn:Hrp;
        destruct (fnfa_state_eqb m r q) eqn:Hrq.
      + apply fnfa_state_eqb_sound in Hrp.
        apply fnfa_state_eqb_sound in Hrq.
        subst. contradiction.
      + apply fnfa_state_eqb_sound in Hrp. subst. lia.
      + apply fnfa_state_eqb_sound in Hrq. subst. lia.
      + lia.
    - apply sum_map_two_mul_le.
      intros r' _.
      apply IH. exact Hneq.
  Qed.

  Lemma accepting_runs_from_word_power_lower :
    forall (m : finite_nfa) q v n w c,
      c <= da_from_to m q v q ->
      Nat.pow c n * accepting_runs_from (fnfa_base m) q w <=
      accepting_runs_from (fnfa_base m) q (word_power v n ++ w).
  Proof.
    intros m q v n.
    induction n as [| n IH]; intros w c Hc; simpl.
    - lia.
    - rewrite <- app_assoc.
      eapply Nat.le_trans with
        (m := da_from_to m q v q *
              accepting_runs_from
                (fnfa_base m) q (word_power v n ++ w)).
      + replace
          (c * Nat.pow c n * accepting_runs_from (fnfa_base m) q w)
          with
          (c * (Nat.pow c n *
             accepting_runs_from (fnfa_base m) q w))
          by lia.
        apply Nat.mul_le_mono.
        * exact Hc.
        * apply IH. exact Hc.
      + unfold da_from_to.
        apply accepting_runs_from_app_lower.
  Qed.

  Lemma ambiguity_of_word_app_lower :
    forall (m : finite_nfa) w_in q w_out,
      start_runs_to m w_in q *
      accepting_runs_from (fnfa_base m) q w_out <=
      ambiguity_of_word (fnfa_base m) (w_in ++ w_out).
  Proof.
    intros m w_in q w_out.
    unfold start_runs_to, ambiguity_of_word.
    apply sum_map_mul_le.
    intros q0 _.
    apply accepting_runs_from_app_lower.
  Qed.

  Lemma ambiguity_of_word_word_power_lower :
    forall (m : finite_nfa) w_in q v n w_out c,
      c <= da_from_to m q v q ->
      start_runs_to m w_in q * Nat.pow c n *
      accepting_runs_from (fnfa_base m) q w_out <=
      ambiguity_of_word
        (fnfa_base m)
        (w_in ++ word_power v n ++ w_out).
  Proof.
    intros m w_in q v n w_out c Hc.
    eapply Nat.le_trans with
      (m := start_runs_to m w_in q *
            accepting_runs_from
              (fnfa_base m) q (word_power v n ++ w_out)).
    - replace
        (start_runs_to m w_in q * Nat.pow c n *
           accepting_runs_from (fnfa_base m) q w_out)
        with
        (start_runs_to m w_in q *
          (Nat.pow c n *
           accepting_runs_from (fnfa_base m) q w_out))
        by lia.
      apply Nat.mul_le_mono_l.
      now apply accepting_runs_from_word_power_lower.
    - apply ambiguity_of_word_app_lower.
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
