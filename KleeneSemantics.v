From Stdlib Require Import List.
Import ListNotations.

From PositionAutomata Require Import Syntax.

Section KleeneSemantics.
  Context {A : Type}.

  Definition marked_symbol : Type := (nat * A)%type.
  (* erase the marks in positioned_regex *)
  Fixpoint erase (r : positioned_regex A) : regex A :=
    match r with
    | PEmpty => Empty
    | PEps => Eps
    | PAtom _ a => Atom a
    | PAlt r1 r2 => Alt (erase r1) (erase r2)
    | PCat r1 r2 => Cat (erase r1) (erase r2)
    | PStar r' => Star (erase r')
    end.

  Fixpoint symbols (mw : list marked_symbol) : list A :=
    match mw with
    | [] => []
    | (_, a) :: mw' => a :: symbols mw'
    end.

  Lemma symbols_app :
    forall mw1 mw2,
      symbols (mw1 ++ mw2) = symbols mw1 ++ symbols mw2.
  Proof.
    induction mw1 as [| [p a] mw1 IH]; intros mw2; simpl; auto.
    now rewrite IH.
  Qed.

  Inductive matches : regex A -> list A -> Prop :=
  | M_Eps :
      matches Eps []
  | M_Atom :
      forall a,
        matches (Atom a) [a]
  | M_AltL :
      forall r1 r2 w,
        matches r1 w ->
        matches (Alt r1 r2) w
  | M_AltR :
      forall r1 r2 w,
        matches r2 w ->
        matches (Alt r1 r2) w
  | M_Cat :
      forall r1 r2 w1 w2,
        matches r1 w1 ->
        matches r2 w2 ->
        matches (Cat r1 r2) (w1 ++ w2)
  | M_Star0 :
      forall r,
        matches (Star r) []
  | M_StarApp :
      forall r w1 w2,
        matches r w1 ->
        w1 <> [] ->
        matches (Star r) w2 ->
        matches (Star r) (w1 ++ w2).

  Inductive matches_marked : positioned_regex A -> list marked_symbol -> Prop :=
  | MM_Eps :
      matches_marked PEps []
  | MM_Atom :
      forall p a,
        matches_marked (PAtom p a) [(p, a)]
  | MM_AltL :
      forall r1 r2 mw,
        matches_marked r1 mw ->
        matches_marked (PAlt r1 r2) mw
  | MM_AltR :
      forall r1 r2 mw,
        matches_marked r2 mw ->
        matches_marked (PAlt r1 r2) mw
  | MM_Cat :
      forall r1 r2 mw1 mw2,
        matches_marked r1 mw1 ->
        matches_marked r2 mw2 ->
        matches_marked (PCat r1 r2) (mw1 ++ mw2)
  | MM_Star0 :
      forall r,
        matches_marked (PStar r) []
  | MM_StarApp :
      forall r mw1 mw2,
        matches_marked r mw1 ->
        mw1 <> [] ->
        matches_marked (PStar r) mw2 ->
        matches_marked (PStar r) (mw1 ++ mw2).

  Lemma erase_label_from :
    forall fresh r,
      erase (fst (label_from fresh r)) = r.
  Proof.
    intros fresh r.
    revert fresh.
    induction r; intros n; simpl; auto.
    - destruct (label_from n r1) as [r1' fresh1] eqn:Hr1.
      destruct (label_from fresh1 r2) as [r2' fresh2] eqn:Hr2.
      specialize (IHr1 n). rewrite Hr1 in IHr1. simpl in IHr1.
      specialize (IHr2 fresh1). rewrite Hr2 in IHr2. simpl in IHr2.
      simpl. rewrite IHr1, IHr2. reflexivity.
    - destruct (label_from n r1) as [r1' fresh1] eqn:Hr1.
      destruct (label_from fresh1 r2) as [r2' fresh2] eqn:Hr2.
      specialize (IHr1 n). rewrite Hr1 in IHr1. simpl in IHr1.
      specialize (IHr2 fresh1). rewrite Hr2 in IHr2. simpl in IHr2.
      simpl. rewrite IHr1, IHr2. reflexivity.
    - destruct (label_from n r) as [r' fresh'] eqn:Hr.
      specialize (IHr n). rewrite Hr in IHr. simpl in IHr.
      simpl. rewrite IHr. reflexivity.
  Qed.

  Corollary erase_label :
    forall r,
      erase (label r) = r.
  Proof.
    intros r. unfold label. apply erase_label_from.
  Qed.

  Lemma matches_marked_symbols :
    forall r mw,
      matches_marked r mw ->
      matches (erase r) (symbols mw).
  Proof.
    intros r mw H.
    induction H; simpl.
    - constructor.
    - constructor.
    - apply M_AltL. exact IHmatches_marked.
    - apply M_AltR. exact IHmatches_marked.
    - rewrite symbols_app. apply M_Cat; assumption.
    - constructor.
    - rewrite symbols_app. eapply M_StarApp; eauto.
      intro Hnil. apply H0.
      destruct mw1 as [| [p a] mw1]; simpl in *.
      + reflexivity.
      + discriminate.
  Qed.

  Lemma label_from_complete :
    forall r w,
      matches r w ->
      forall fresh,
      exists mw,
        symbols mw = w /\
        matches_marked (fst (label_from fresh r)) mw.
  Proof.
    intros r w Hmatch.
    induction Hmatch; intros fresh.
    - exists []. simpl. split; auto. constructor.
    - exists [(fresh, a)]. simpl. split; auto. constructor.
    - destruct (IHHmatch fresh) as [mw [Hsym Hm]].
      destruct (label_from fresh r1) as [r1' n1] eqn:Hr1.
      destruct (label_from n1 r2) as [r2' n2] eqn:Hr2.
      simpl in Hm |- *.
      exists mw. split; auto.
      replace
        (fst
           (let (r1', fresh1) := label_from fresh r1 in
            let (r2', fresh2) := label_from fresh1 r2 in (PAlt r1' r2', fresh2)))
        with (PAlt r1' r2')
        by (rewrite Hr1, Hr2; reflexivity).
      now apply MM_AltL.
    - destruct (label_from fresh r1) as [r1' n1] eqn:Hr1.
      destruct (IHHmatch n1) as [mw [Hsym Hm]].
      destruct (label_from n1 r2) as [r2' n2] eqn:Hr2.
      simpl in Hm |- *.
      exists mw. split; auto.
      replace
        (fst
           (let (r1', fresh1) := label_from fresh r1 in
            let (r2', fresh2) := label_from fresh1 r2 in (PAlt r1' r2', fresh2)))
        with (PAlt r1' r2')
        by (rewrite Hr1, Hr2; reflexivity).
      now apply MM_AltR.
    - destruct (IHHmatch1 fresh) as [mw1 [Hsym1 Hm1]].
      destruct (label_from fresh r1) as [r1' n1] eqn:Hr1.
      simpl in Hm1.
      destruct (IHHmatch2 n1) as [mw2 [Hsym2 Hm2]].
      destruct (label_from n1 r2) as [r2' n2] eqn:Hr2.
      simpl in Hm2 |- *.
      exists (mw1 ++ mw2). split.
      + rewrite symbols_app. now rewrite Hsym1, Hsym2.
      + replace
          (fst
             (let (r1', fresh1) := label_from fresh r1 in
              let (r2', fresh2) := label_from fresh1 r2 in (PCat r1' r2', fresh2)))
          with (PCat r1' r2')
          by (rewrite Hr1, Hr2; reflexivity).
        now constructor.
    - destruct (label_from fresh r) as [r' n] eqn:Hr.
      exists []. split; auto.
      replace
        (fst (label_from fresh (Star r)))
        with (PStar r')
        by (simpl; rewrite Hr; reflexivity).
      apply MM_Star0.
    - destruct (IHHmatch1 fresh) as [mw1 [Hsym1 Hm1]].
      destruct (label_from fresh r) as [r' n] eqn:Hr.
      simpl in Hm1.
      destruct (IHHmatch2 fresh) as [mw2 [Hsym2 Hm2]].
      replace
        (fst (label_from fresh (Star r)))
        with (PStar r')
        in Hm2
        by (simpl; rewrite Hr; reflexivity).
      exists (mw1 ++ mw2). split.
      + rewrite symbols_app. now rewrite Hsym1, Hsym2.
      + replace
          (fst (label_from fresh (Star r)))
          with (PStar r')
          by (simpl; rewrite Hr; reflexivity).
        apply MM_StarApp.
        * exact Hm1.
        * intro Hnil.
          match goal with
          | Hne : ?w <> [] |- _ =>
              destruct mw1 as [| x mw1]
              ; [ simpl in Hsym1; subst; exfalso; apply Hne; reflexivity
                | simpl in Hnil; discriminate ]
          end.
        * exact Hm2.
  Qed.

  Theorem label_semantics_preserved :
    forall r w,
      matches r w ->
      exists mw,
        symbols mw = w /\
        matches_marked (label r) mw.
  Proof.
    intros r w Hmatch.
    destruct (label_from_complete r w Hmatch 0) as [mw [Hsym Hm]].
    exists mw. split; auto.
  Qed.

  Theorem marked_semantics_reflects :
    forall r mw,
      matches_marked (label r) mw ->
      matches r (symbols mw).
  Proof.
    intros r mw Hm.
    pose proof (matches_marked_symbols (label r) mw Hm) as H.
    rewrite (erase_label r) in H.
    exact H.
  Qed.
End KleeneSemantics.
