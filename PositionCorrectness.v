Require Import List Arith Lia.
Import ListNotations.

From PositionAutomata Require Import Sets Syntax PositionAutomaton KleeneSemantics.

Section PositionCorrectness.
  Context {A : Type}.

  Fixpoint atom_count (r : regex A) : nat :=
    match r with
    | Empty | Eps => 0
    | Atom _ => 1
    | Alt r1 r2 | Cat r1 r2 => atom_count r1 + atom_count r2
    | Star r' => atom_count r'
    end.

  Lemma next_position_from :
    forall fresh r,
      snd (label_from fresh r) = fresh + atom_count r.
  Proof.
    intros fresh r.
    revert fresh.
    induction r; intros n; simpl; try lia.
    - destruct (label_from n r1) as [r1' n1] eqn:Hr1.
      destruct (label_from n1 r2) as [r2' n2] eqn:Hr2.
      simpl.
      specialize (IHr1 n).
      rewrite Hr1 in IHr1. simpl in IHr1.
      specialize (IHr2 n1).
      rewrite Hr2 in IHr2. simpl in IHr2.
      subst n1 n2.
      lia.
    - destruct (label_from n r1) as [r1' n1] eqn:Hr1.
      destruct (label_from n1 r2) as [r2' n2] eqn:Hr2.
      simpl.
      specialize (IHr1 n).
      rewrite Hr1 in IHr1. simpl in IHr1.
      specialize (IHr2 n1).
      rewrite Hr2 in IHr2. simpl in IHr2.
      subst n1 n2.
      lia.
    - destruct (label_from n r) as [r' n'] eqn:Hr.
      simpl.
      specialize (IHr n).
      rewrite Hr in IHr. simpl in IHr.
      subst n'.
      lia.
  Qed.

  Lemma positions_label_from :
    forall fresh r,
      positions (fst (label_from fresh r)) = seq fresh (atom_count r).
  Proof.
    intros fresh r.
    revert fresh.
    induction r; intros n; simpl.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - destruct (label_from n r1) as [r1' n1] eqn:Hr1.
      destruct (label_from n1 r2) as [r2' n2] eqn:Hr2.
      simpl.
      specialize (IHr1 n).
      rewrite Hr1 in IHr1. simpl in IHr1.
      specialize (IHr2 n1).
      rewrite Hr2 in IHr2. simpl in IHr2.
      pose proof (next_position_from n r1) as Hn1.
      rewrite Hr1 in Hn1. simpl in Hn1.
      rewrite IHr1, IHr2.
      subst n1.
      rewrite seq_app. reflexivity.
    - destruct (label_from n r1) as [r1' n1] eqn:Hr1.
      destruct (label_from n1 r2) as [r2' n2] eqn:Hr2.
      simpl.
      specialize (IHr1 n).
      rewrite Hr1 in IHr1. simpl in IHr1.
      specialize (IHr2 n1).
      rewrite Hr2 in IHr2. simpl in IHr2.
      pose proof (next_position_from n r1) as Hn1.
      rewrite Hr1 in Hn1. simpl in Hn1.
      rewrite IHr1, IHr2.
      subst n1.
      rewrite seq_app. reflexivity.
    - destruct (label_from n r) as [r' n'] eqn:Hr.
      simpl.
      specialize (IHr n).
      rewrite Hr in IHr. simpl in IHr.
      rewrite IHr.
      reflexivity.
  Qed.

  Corollary positions_label :
    forall r,
      positions (label r) = seq 0 (atom_count r).
  Proof.
    intros r. unfold label. apply positions_label_from.
  Qed.

  Corollary label_positions_nodup :
    forall r : regex A,
      NoDup (positions (label r)).
  Proof.
    intros r.
    rewrite positions_label.
    apply seq_NoDup.
  Qed.

  Lemma atoms_positions :
    forall pr : positioned_regex A,
      map fst (atoms pr) = positions pr.
  Proof.
    induction pr; simpl; try rewrite IHpr; try rewrite IHpr1; try rewrite IHpr2; try reflexivity.
    - rewrite map_app, IHpr1, IHpr2. reflexivity.
    - rewrite map_app, IHpr1, IHpr2. reflexivity.
  Qed.

  Lemma lookup_symbol_complete :
    forall (ats : list (nat * A)) p a,
      NoDup (map fst ats) ->
      In (p, a) ats ->
      lookup_symbol p ats = Some a.
  Proof.
    induction ats as [| [q b] ats IH]; simpl; intros p a Hnodup Hin.
    - contradiction.
    - inversion Hnodup as [| x xs Hnotin Hnodup']; subst.
      destruct Hin as [Heq | Hin].
      + inversion Heq; subst.
        rewrite Nat.eqb_refl. reflexivity.
      + destruct (Nat.eqb p q) eqn:Hpq.
        * apply Nat.eqb_eq in Hpq. subst.
          exfalso. apply Hnotin.
          apply in_map_iff.
          exists (q, a). split; [reflexivity | exact Hin].
        * apply IH; auto.
  Qed.

  Lemma label_of_complete :
    forall (pr : positioned_regex A) p a,
      NoDup (positions pr) ->
      In (p, a) (atoms pr) ->
      label_of pr p = Some a.
  Proof.
    intros pr p a Hnodup Hin.
    unfold label_of.
    apply lookup_symbol_complete.
    - rewrite atoms_positions. exact Hnodup.
    - exact Hin.
  Qed.

  Lemma matches_marked_in_atoms :
    forall (pr : positioned_regex A) mw,
      matches_marked pr mw ->
      Forall (fun pa => In pa (atoms pr)) mw.
  Proof.
    intros pr mw Hm.
    induction Hm; simpl.
    - constructor.
    - constructor; [left; reflexivity | constructor].
    - eapply Forall_impl; [| exact IHHm].
      intros x Hin. apply in_or_app. now left.
    - eapply Forall_impl; [| exact IHHm].
      intros x Hin. apply in_or_app. now right.
    - rewrite Forall_app. split.
      + eapply Forall_impl; [| exact IHHm1].
        intros x Hin. apply in_or_app. now left.
      + eapply Forall_impl; [| exact IHHm2].
        intros x Hin. apply in_or_app. now right.
    - constructor.
    - rewrite Forall_app. split.
      + exact IHHm1.
      + eapply Forall_impl; [| exact IHHm2].
        intros x Hin. exact Hin.
  Qed.

  Lemma matches_marked_nullable :
    forall (pr : positioned_regex A),
      matches_marked pr [] ->
      nullable pr = true.
  Proof.
    intros pr Hm.
    remember ([] : list marked_symbol) as w eqn:Hw.
    revert Hw.
    induction Hm; intros Hw; subst; simpl; auto.
    - discriminate.
    - rewrite (IHHm eq_refl). reflexivity.
    - rewrite (IHHm eq_refl). destruct (nullable r1); reflexivity.
    - apply app_eq_nil in Hw as [Hw1 Hw2].
      rewrite (IHHm1 Hw1), (IHHm2 Hw2). reflexivity.
  Qed.

End PositionCorrectness.
