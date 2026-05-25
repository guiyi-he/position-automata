From Stdlib Require Import List Arith Lia.
Import ListNotations.

From PositionAutomata Require Import
  Sets Syntax PositionAutomaton KleeneSemantics DegreeofAmbiguity.

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

  Lemma nullable_matches_marked :
    forall (pr : positioned_regex A),
      nullable pr = true ->
      matches_marked pr [].
  Proof.
    induction pr; simpl; intros Hnull; try discriminate.
    - constructor.
    - apply Bool.orb_true_iff in Hnull as [Hnull | Hnull].
      + apply MM_AltL. now apply IHpr1.
      + apply MM_AltR. now apply IHpr2.
    - apply Bool.andb_true_iff in Hnull as [Hnull1 Hnull2].
      change (matches_marked (PCat pr1 pr2)
        (([] : list (nat * A)) ++ ([] : list (nat * A)))).
      apply MM_Cat; auto.
    - constructor.
  Qed.

  Lemma matches_marked_firstpos :
    forall (pr : positioned_regex A) mw,
      matches_marked pr mw ->
      forall p a rest,
        mw = (p, a) :: rest ->
        mem p (firstpos pr) = true.
  Proof.
    intros pr mw Hm.
    induction Hm; intros p0 a0 rest Heq; simpl in *; try discriminate.
    - inversion Heq; subst. simpl. rewrite Nat.eqb_refl. reflexivity.
    - apply mem_union_left. eapply IHHm; eauto.
    - apply mem_union_right. eapply IHHm; eauto.
    - destruct mw1 as [| [p1 a1] mw1'].
      + simpl in Heq. subst.
        rewrite (matches_marked_nullable r1 Hm1).
        apply mem_union_right. eapply IHHm2; reflexivity.
      + inversion Heq; subst.
        destruct (nullable r1) eqn:Hnull.
        * apply mem_union_left. eapply IHHm1; reflexivity.
        * eapply IHHm1; reflexivity.
    - destruct mw1 as [| [p1 a1] mw1']; [contradiction |].
      inversion Heq; subst.
      eapply IHHm1; reflexivity.
  Qed.

  Fixpoint last_position_from
      (p : nat)
      (mw : list (nat * A)) : nat :=
    match mw with
    | [] => p
    | (q, _) :: mw' => last_position_from q mw'
    end.

  Lemma last_position_from_app_nonempty :
    forall prefix p q b suffix,
      last_position_from p (prefix ++ (q, b) :: suffix) =
        last_position_from q suffix.
  Proof.
    induction prefix as [| [r c] prefix IH]; intros p q b suffix; simpl; auto.
  Qed.

  Lemma matches_marked_lastpos :
    forall (pr : positioned_regex A) mw,
      matches_marked pr mw ->
      forall p a rest,
        mw = (p, a) :: rest ->
        mem (last_position_from p rest) (lastpos pr) = true.
  Proof.
    intros pr mw Hm.
    induction Hm; intros p0 a0 rest Heq; simpl in *; try discriminate.
    - inversion Heq; subst. simpl. rewrite Nat.eqb_refl. reflexivity.
    - apply mem_union_left. eapply IHHm; eauto.
    - apply mem_union_right. eapply IHHm; eauto.
    - destruct mw2 as [| [q b] mw2'].
      + rewrite app_nil_r in Heq.
        rewrite (matches_marked_nullable r2 Hm2).
        apply mem_union_left. eapply IHHm1; eauto.
      + destruct mw1 as [| [p1 a1] mw1'].
        * simpl in Heq. inversion Heq; subst.
          destruct (nullable r2) eqn:Hnull.
          -- apply mem_union_right. eapply IHHm2; reflexivity.
          -- eapply IHHm2; reflexivity.
        * inversion Heq; subst.
          rewrite last_position_from_app_nonempty.
          destruct (nullable r2) eqn:Hnull.
          -- apply mem_union_right. eapply IHHm2; reflexivity.
          -- eapply IHHm2; reflexivity.
    - destruct mw2 as [| [q b] mw2'].
      + rewrite app_nil_r in Heq.
        eapply IHHm1; eauto.
      + destruct mw1 as [| [p1 a1] mw1']; [contradiction |].
        inversion Heq; subst.
        rewrite last_position_from_app_nonempty.
        eapply IHHm2; reflexivity.
  Qed.

  Lemma matches_marked_head_label :
    forall (pr : positioned_regex A) p a rest,
      NoDup (positions pr) ->
      matches_marked pr ((p, a) :: rest) ->
      label_of pr p = Some a.
  Proof.
    intros pr p a rest Hnodup Hm.
    pose proof (matches_marked_in_atoms pr ((p, a) :: rest) Hm) as Hatoms.
    inversion Hatoms as [| x xs Hhead _]; subst.
    eapply label_of_complete; eauto.
  Qed.

  Theorem matches_marked_accepts_marked_boundary :
    forall (pr : positioned_regex A) mw,
      NoDup (positions pr) ->
      matches_marked pr mw ->
      match mw with
      | [] => nullable pr = true
      | (p, a) :: rest =>
          mem p (firstpos pr) = true /\
          label_of pr p = Some a /\
          mem (last_position_from p rest) (lastpos pr) = true
      end.
  Proof.
    intros pr mw Hnodup Hm.
    destruct mw as [| [p a] rest].
    - now apply matches_marked_nullable.
    - repeat split.
      + eapply matches_marked_firstpos; eauto.
      + eapply matches_marked_head_label; eauto.
      + eapply matches_marked_lastpos; eauto.
  Qed.

  Lemma lookup_follow_add_follow_preserve :
    forall p q x xs t,
      mem q (lookup_follow p t) = true ->
      mem q (lookup_follow p (add_follow x xs t)) = true.
  Proof.
    intros p q x xs t.
    induction t as [| [y ys] t IH]; simpl; intros H.
    - discriminate.
    - destruct (Nat.eqb p y) eqn:Hpy.
      + destruct (Nat.eqb x y) eqn:Hxy; simpl; rewrite Hpy; auto.
        apply mem_union_right. exact H.
      + destruct (Nat.eqb x y) eqn:Hxy; simpl; rewrite Hpy; auto.
  Qed.

  Lemma lookup_follow_add_follow_hit :
    forall p q xs t,
      mem q xs = true ->
      mem q (lookup_follow p (add_follow p xs t)) = true.
  Proof.
    intros p q xs t.
    induction t as [| [y ys] t IH]; simpl; intros Hmem.
    - rewrite Nat.eqb_refl. exact Hmem.
    - destruct (Nat.eqb p y) eqn:Hpy; simpl; rewrite Hpy; auto.
      apply mem_union_left. exact Hmem.
  Qed.

  Lemma lookup_follow_add_follow_all_preserve :
    forall from to_ t p q,
      mem q (lookup_follow p t) = true ->
      mem q (lookup_follow p (add_follow_all from to_ t)) = true.
  Proof.
    induction from as [| x from IH]; simpl; intros to_ t p q H.
    - exact H.
    - apply IH. now apply lookup_follow_add_follow_preserve.
  Qed.

  Lemma lookup_follow_add_follow_all_hit :
    forall from to_ t p q,
      mem p from = true ->
      mem q to_ = true ->
      mem q (lookup_follow p (add_follow_all from to_ t)) = true.
  Proof.
    induction from as [| x from IH]; simpl; intros to_ t p q Hfrom Hto.
    - discriminate.
    - apply Bool.orb_true_iff in Hfrom as [Heq | Hfrom].
      + apply Nat.eqb_eq in Heq. subst x.
        apply lookup_follow_add_follow_all_preserve.
        now apply lookup_follow_add_follow_hit.
      + apply IH; auto.
  Qed.

  Lemma lookup_follow_app_left :
    forall p q t1 t2,
      mem q (lookup_follow p t1) = true ->
      mem q (lookup_follow p (t1 ++ t2)) = true.
  Proof.
    intros p q t1.
    induction t1 as [| [x xs] t1 IH]; simpl; intros t2 H.
    - discriminate.
    - destruct (Nat.eqb p x) eqn:Hpx; auto.
  Qed.

  Lemma lookup_follow_app_right :
    forall p t1 t2,
      (forall xs, ~ In (p, xs) t1) ->
      lookup_follow p (t1 ++ t2) = lookup_follow p t2.
  Proof.
    intros p t1.
    induction t1 as [| [x xs] t1 IH]; simpl; intros t2 Hnotin.
    - reflexivity.
    - destruct (Nat.eqb p x) eqn:Hpx.
      + apply Nat.eqb_eq in Hpx. subst x.
        exfalso. apply (Hnotin xs). now left.
      + apply IH. intros ys Hin.
        apply (Hnotin ys). now right.
  Qed.

  Lemma lookup_follow_app_right_preserve :
    forall p q t1 t2,
      (forall xs, ~ In (p, xs) t1) ->
      mem q (lookup_follow p t2) = true ->
      mem q (lookup_follow p (t1 ++ t2)) = true.
  Proof.
    intros p q t1 t2 Hnotin H.
    rewrite lookup_follow_app_right; auto.
  Qed.

  Lemma lookup_follow_mem_key :
    forall p q t,
      mem q (lookup_follow p t) = true ->
      exists ps, In (p, ps) t.
  Proof.
    intros p q t.
    induction t as [| [x xs] t IH]; simpl; intros H.
    - discriminate.
    - destruct (Nat.eqb p x) eqn:Hpx.
      + apply Nat.eqb_eq in Hpx. subst x.
        exists xs. now left.
      + destruct (IH H) as [ps Hin].
        exists ps. now right.
  Qed.

  Lemma In_add_elim :
    forall x y xs,
      In x (add y xs) ->
      x = y \/ In x xs.
  Proof.
    intros x y xs Hin.
    unfold add in Hin.
    destruct (mem y xs); simpl in Hin; auto.
    destruct Hin as [Heq | Hin]; auto.
  Qed.

  Lemma In_union_elim :
    forall x xs ys,
      In x (union xs ys) ->
      In x xs \/ In x ys.
  Proof.
    intros x xs.
    induction xs as [| y xs IH]; simpl; intros ys Hin.
    - auto.
    - apply In_add_elim in Hin as [Heq | Hin].
      + subst. auto.
      + apply IH in Hin as [Hin | Hin]; auto.
  Qed.

  Lemma firstpos_In_positions :
    forall (r : positioned_regex A) p,
      In p (firstpos r) ->
      In p (positions r).
  Proof.
    induction r; simpl; intros p Hin; auto.
    - apply In_union_elim in Hin as [Hin | Hin].
      + apply in_or_app. left. now apply IHr1.
      + apply in_or_app. right. now apply IHr2.
    - destruct (nullable r1) eqn:Hnull.
      + apply In_union_elim in Hin as [Hin | Hin].
        * apply in_or_app. left. now apply IHr1.
        * apply in_or_app. right. now apply IHr2.
      + apply in_or_app. left. now apply IHr1.
  Qed.

  Lemma lastpos_In_positions :
    forall (r : positioned_regex A) p,
      In p (lastpos r) ->
      In p (positions r).
  Proof.
    induction r; simpl; intros p Hin; auto.
    - apply In_union_elim in Hin as [Hin | Hin].
      + apply in_or_app. left. now apply IHr1.
      + apply in_or_app. right. now apply IHr2.
    - destruct (nullable r2) eqn:Hnull.
      + apply In_union_elim in Hin as [Hin | Hin].
        * apply in_or_app. left. now apply IHr1.
        * apply in_or_app. right. now apply IHr2.
      + apply in_or_app. right. now apply IHr2.
  Qed.

  Lemma add_follow_key_in :
    forall x xs t p ys,
      In (p, ys) (add_follow x xs t) ->
      p = x \/ exists zs, In (p, zs) t.
  Proof.
    intros x xs t.
    induction t as [| [y zs] t IH]; simpl; intros p ys Hin.
    - destruct Hin as [Heq | []].
      inversion Heq. auto.
    - destruct (Nat.eqb x y) eqn:Hxy.
      + destruct Hin as [Heq | Hin].
        * inversion Heq; subst.
          apply Nat.eqb_eq in Hxy. subst. auto.
        * right. exists ys. now right.
      + destruct Hin as [Heq | Hin].
        * inversion Heq; subst.
          right. exists ys. now left.
        * apply IH in Hin as [Heq | [ws Hin]]; auto.
          right. exists ws. now right.
  Qed.

  Lemma add_follow_all_key_in :
    forall from to_ t p ys,
      In (p, ys) (add_follow_all from to_ t) ->
      In p from \/ exists zs, In (p, zs) t.
  Proof.
    induction from as [| x from IH]; simpl; intros to_ t p ys Hin.
    - right. exists ys. exact Hin.
    - apply IH in Hin as [Hin | [zs Hin]].
      + auto.
      + apply add_follow_key_in in Hin as [Heq | [ws Hin]].
        * subst. auto.
        * right. exists ws. exact Hin.
  Qed.

  Lemma followpos_key_in_positions :
    forall (r : positioned_regex A) p ps,
      In (p, ps) (followpos r) ->
      In p (positions r).
  Proof.
    induction r; simpl; intros p ps Hin; try contradiction.
    - apply in_app_iff in Hin as [Hin | Hin].
      + apply in_or_app. left. eapply IHr1; eauto.
      + apply in_or_app. right. eapply IHr2; eauto.
    - apply add_follow_all_key_in in Hin as [Hin | [zs Hin]].
      + apply in_or_app. left. now apply lastpos_In_positions.
      + apply in_app_iff in Hin as [Hin | Hin].
        * apply in_or_app. left. eapply IHr1; eauto.
        * apply in_or_app. right. eapply IHr2; eauto.
    - apply add_follow_all_key_in in Hin as [Hin | [zs Hin]].
      + now apply lastpos_In_positions.
      + eapply IHr; eauto.
  Qed.

  Lemma NoDup_app_not_both :
    forall (xs ys : list nat) x,
      NoDup (xs ++ ys) ->
      In x xs ->
      In x ys ->
      False.
  Proof.
    induction xs as [| y xs IH]; simpl; intros ys x Hnodup Hin_xs Hin_ys.
    - contradiction.
    - inversion Hnodup as [| z zs Hnotin Hnodup']; subst.
      destruct Hin_xs as [Heq | Hin_xs].
      + subst y. apply Hnotin. apply in_or_app. now right.
      + eapply IH; eauto.
  Qed.

  Lemma NoDup_app_left :
    forall (xs ys : list nat),
      NoDup (xs ++ ys) ->
      NoDup xs.
  Proof.
    induction xs as [| x xs IH]; simpl; intros ys Hnodup.
    - constructor.
    - inversion Hnodup as [| y zs Hnotin Hnodup']; subst.
      constructor.
      + intros Hin. apply Hnotin. apply in_or_app. now left.
      + now apply IH with (ys := ys).
  Qed.

  Lemma NoDup_app_right :
    forall (xs ys : list nat),
      NoDup (xs ++ ys) ->
      NoDup ys.
  Proof.
    induction xs as [| x xs IH]; simpl; intros ys Hnodup.
    - exact Hnodup.
    - inversion Hnodup as [| y zs Hnotin Hnodup']; subst.
      now apply IH.
  Qed.

  Lemma mem_true_In :
    forall x xs,
      mem x xs = true ->
      In x xs.
  Proof.
    intros x xs.
    induction xs as [| y xs IH]; simpl; intros H; try discriminate.
    apply Bool.orb_true_iff in H as [H | H].
    - apply Nat.eqb_eq in H. subst. now left.
    - right. now apply IH.
  Qed.

  Lemma In_mem :
    forall x xs,
      In x xs ->
      mem x xs = true.
  Proof.
    intros x xs.
    induction xs as [| y xs IH]; simpl; intros Hin; try contradiction.
    destruct Hin as [Heq | Hin].
    - subst. rewrite Nat.eqb_refl. reflexivity.
    - apply Bool.orb_true_iff. right. now apply IH.
  Qed.

  Lemma mem_union_elim :
    forall x xs ys,
      mem x (union xs ys) = true ->
      mem x xs = true \/ mem x ys = true.
  Proof.
    intros x xs ys Hmem.
    apply mem_true_In in Hmem.
    apply In_union_elim in Hmem as [Hin | Hin].
    - left. now apply In_mem.
    - right. now apply In_mem.
  Qed.

  Lemma lookup_follow_no_key :
    forall p t,
      (forall ps, ~ In (p, ps) t) ->
      lookup_follow p t = [].
  Proof.
    intros p t.
    induction t as [| [q qs] t IH]; simpl; intros Hnotin.
    - reflexivity.
    - destruct (Nat.eqb p q) eqn:Hq.
      + apply Nat.eqb_eq in Hq. subst q.
        exfalso. apply (Hnotin qs). now left.
      + apply IH. intros ps Hin.
        apply (Hnotin ps). now right.
  Qed.

  Lemma mem_lookup_follow_key_in_positions :
    forall (r : positioned_regex A) p q,
      mem q (lookup_follow p (followpos r)) = true ->
      In p (positions r).
  Proof.
    intros r p q H.
    destruct (lookup_follow_mem_key p q (followpos r) H) as [ps Hkey].
    eapply followpos_key_in_positions; eauto.
  Qed.

  Lemma lookup_follow_mem_entry :
    forall p q t,
      mem q (lookup_follow p t) = true ->
      exists ps,
        In (p, ps) t /\ In q ps.
  Proof.
    intros p q t.
    induction t as [| [x xs] t IH]; simpl; intros H; try discriminate.
    destruct (Nat.eqb p x) eqn:Hpx.
    - apply Nat.eqb_eq in Hpx. subst x.
      exists xs. split; auto.
      now apply mem_true_In.
    - destruct (IH H) as [ps [Hin Hq]].
      exists ps. split; auto.
  Qed.

  Lemma add_follow_values_in :
    forall pos x xs t,
      (forall q, In q xs -> In q pos) ->
      (forall p ps q, In (p, ps) t -> In q ps -> In q pos) ->
      forall p ps q,
        In (p, ps) (add_follow x xs t) ->
        In q ps ->
        In q pos.
  Proof.
    intros pos x xs t Hxs Ht.
    induction t as [| [y ys] t IH]; simpl; intros p ps q Hin Hq.
    - destruct Hin as [Heq | []].
      inversion Heq; subst. now apply Hxs.
    - destruct (Nat.eqb x y) eqn:Hxy.
      + destruct Hin as [Heq | Hin].
        * inversion Heq; subst.
          apply In_union_elim in Hq as [Hq | Hq].
          -- now apply Hxs.
          -- eapply Ht; [left; reflexivity | exact Hq].
        * eapply Ht; [right; exact Hin | exact Hq].
      + destruct Hin as [Heq | Hin].
        * inversion Heq; subst.
          eapply Ht; [left; reflexivity | exact Hq].
        * eapply IH; eauto.
          intros p0 ps0 q0 Hin0 Hq0.
          apply (Ht p0 ps0 q0); [right; exact Hin0 | exact Hq0].
  Qed.

  Lemma add_follow_all_values_in :
    forall pos from to_ t,
      (forall q, In q to_ -> In q pos) ->
      (forall p ps q, In (p, ps) t -> In q ps -> In q pos) ->
      forall p ps q,
        In (p, ps) (add_follow_all from to_ t) ->
        In q ps ->
        In q pos.
  Proof.
    intros pos from.
    induction from as [| x from IH]; simpl; intros to_ t Hto Ht p ps q Hin Hq.
    - eapply Ht; eauto.
    - eapply (IH to_ (add_follow x to_ t)); eauto.
      intros p0 ps0 q0 Hin0 Hq0.
      eapply add_follow_values_in; eauto.
  Qed.

  Lemma followpos_values_in_positions :
    forall (r : positioned_regex A) p ps q,
      In (p, ps) (followpos r) ->
      In q ps ->
      In q (positions r).
  Proof.
    induction r; simpl; intros p ps q Hin Hq; try contradiction.
    - apply in_app_iff in Hin as [Hin | Hin].
      + apply in_or_app. left. eapply IHr1; eauto.
      + apply in_or_app. right. eapply IHr2; eauto.
    - eapply (add_follow_all_values_in
        (positions r1 ++ positions r2)
        (lastpos r1)
        (firstpos r2)
        (followpos r1 ++ followpos r2)); eauto.
      + intros x Hx. apply in_or_app. right. now apply firstpos_In_positions.
      + intros p0 ps0 q0 Hin0 Hq0.
        apply in_app_iff in Hin0 as [Hin0 | Hin0].
        * apply in_or_app. left. eapply IHr1; eauto.
        * apply in_or_app. right. eapply IHr2; eauto.
    - eapply (add_follow_all_values_in
        (positions r)
        (lastpos r)
        (firstpos r)
        (followpos r)); eauto.
      intros x Hx. now apply firstpos_In_positions.
  Qed.

  Lemma mem_lookup_follow_value_in_positions :
    forall (r : positioned_regex A) p q,
      mem q (lookup_follow p (followpos r)) = true ->
      In q (positions r).
  Proof.
    intros r p q H.
    destruct (lookup_follow_mem_entry p q (followpos r) H) as [ps [Hin Hq]].
    eapply followpos_values_in_positions; eauto.
  Qed.

  Lemma lookup_follow_app_no_key_right :
    forall p t1 t2,
      (forall ps, ~ In (p, ps) t2) ->
      lookup_follow p (t1 ++ t2) = lookup_follow p t1.
  Proof.
    intros p t1.
    induction t1 as [| [q qs] t1 IH]; simpl; intros t2 Hnotin.
    - now apply lookup_follow_no_key.
    - destruct (Nat.eqb p q); auto.
  Qed.

  Lemma lookup_follow_app_left_reflect :
    forall (r1 r2 : positioned_regex A) p q,
      NoDup (positions r1 ++ positions r2) ->
      In p (positions r1) ->
      mem q (lookup_follow p (followpos r1 ++ followpos r2)) = true ->
      mem q (lookup_follow p (followpos r1)) = true.
  Proof.
    intros r1 r2 p q Hnodup Hpin H.
    rewrite lookup_follow_app_no_key_right in H; auto.
    intros ps Hin.
    pose proof (followpos_key_in_positions r2 p ps Hin) as Hpin2.
    eapply NoDup_app_not_both; eauto.
  Qed.

  Lemma lookup_follow_app_right_reflect :
    forall (r1 r2 : positioned_regex A) p q,
      NoDup (positions r1 ++ positions r2) ->
      In p (positions r2) ->
      mem q (lookup_follow p (followpos r1 ++ followpos r2)) = true ->
      mem q (lookup_follow p (followpos r2)) = true.
  Proof.
    intros r1 r2 p q Hnodup Hpin H.
    rewrite lookup_follow_app_right in H.
    - exact H.
    - intros ps Hin.
      pose proof (followpos_key_in_positions r1 p ps Hin) as Hpin1.
      eapply NoDup_app_not_both; eauto.
  Qed.

  Lemma followpos_cat_boundary :
    forall (r1 r2 : positioned_regex A) p q,
      mem p (lastpos r1) = true ->
      mem q (firstpos r2) = true ->
      mem q (lookup_follow p (followpos (PCat r1 r2))) = true.
  Proof.
    intros r1 r2 p q Hlast Hfirst.
    simpl.
    now apply lookup_follow_add_follow_all_hit.
  Qed.

  Lemma followpos_alt_left_preserve :
    forall (r1 r2 : positioned_regex A) p q,
      mem q (lookup_follow p (followpos r1)) = true ->
      mem q (lookup_follow p (followpos (PAlt r1 r2))) = true.
  Proof.
    intros r1 r2 p q H.
    simpl.
    now apply lookup_follow_app_left.
  Qed.

  Lemma followpos_alt_right_preserve :
    forall (r1 r2 : positioned_regex A) p q,
      NoDup (positions (PAlt r1 r2)) ->
      mem q (lookup_follow p (followpos r2)) = true ->
      mem q (lookup_follow p (followpos (PAlt r1 r2))) = true.
  Proof.
    intros r1 r2 p q Hnodup H.
    simpl.
    apply lookup_follow_app_right_preserve; auto.
    intros xs Hin.
    destruct (lookup_follow_mem_key p q (followpos r2) H) as [ys Hkey2].
    pose proof (followpos_key_in_positions r1 p xs Hin) as Hin1.
    pose proof (followpos_key_in_positions r2 p ys Hkey2) as Hin2.
    eapply NoDup_app_not_both; eauto.
  Qed.

  Lemma followpos_star_boundary :
    forall (r : positioned_regex A) p q,
      mem p (lastpos r) = true ->
      mem q (firstpos r) = true ->
      mem q (lookup_follow p (followpos (PStar r))) = true.
  Proof.
    intros r p q Hlast Hfirst.
    simpl.
    now apply lookup_follow_add_follow_all_hit.
  Qed.

  Lemma followpos_cat_left_preserve :
    forall (r1 r2 : positioned_regex A) p q,
      mem q (lookup_follow p (followpos r1)) = true ->
      mem q (lookup_follow p (followpos (PCat r1 r2))) = true.
  Proof.
    intros r1 r2 p q H.
    simpl.
    apply lookup_follow_add_follow_all_preserve.
    now apply lookup_follow_app_left.
  Qed.

  Lemma followpos_cat_right_preserve :
    forall (r1 r2 : positioned_regex A) p q,
      NoDup (positions (PCat r1 r2)) ->
      mem q (lookup_follow p (followpos r2)) = true ->
      mem q (lookup_follow p (followpos (PCat r1 r2))) = true.
  Proof.
    intros r1 r2 p q Hnodup H.
    simpl.
    apply lookup_follow_add_follow_all_preserve.
    apply lookup_follow_app_right_preserve; auto.
    intros xs Hin.
    destruct (lookup_follow_mem_key p q (followpos r2) H) as [ys Hkey2].
    pose proof (followpos_key_in_positions r1 p xs Hin) as Hin1.
    pose proof (followpos_key_in_positions r2 p ys Hkey2) as Hin2.
    eapply NoDup_app_not_both; eauto.
  Qed.

  Lemma followpos_star_preserve :
    forall (r : positioned_regex A) p q,
      mem q (lookup_follow p (followpos r)) = true ->
      mem q (lookup_follow p (followpos (PStar r))) = true.
  Proof.
    intros r p q H.
    simpl.
    now apply lookup_follow_add_follow_all_preserve.
  Qed.

  Lemma lookup_symbol_app_left :
    forall p (a : A) (xs ys : list (nat * A)),
      lookup_symbol p xs = Some a ->
      lookup_symbol p (xs ++ ys) = Some a.
  Proof.
    intros p a xs.
    induction xs as [| [q b] xs IH]; simpl; intros ys H; try discriminate.
    destruct (Nat.eqb p q); auto.
  Qed.

  Lemma lookup_symbol_app_right :
    forall p (xs ys : list (nat * A)),
      (forall a, ~ In (p, a) xs) ->
      lookup_symbol p (xs ++ ys) = lookup_symbol p ys.
  Proof.
    intros p xs.
    induction xs as [| [q b] xs IH]; simpl; intros ys Hnotin.
    - reflexivity.
    - destruct (Nat.eqb p q) eqn:Hpq.
      + apply Nat.eqb_eq in Hpq. subst q.
        exfalso. apply (Hnotin b). now left.
      + apply IH. intros a Hin.
        apply (Hnotin a). now right.
  Qed.

  Lemma lookup_symbol_key_in :
    forall p (a : A) (xs : list (nat * A)),
      lookup_symbol p xs = Some a ->
      In (p, a) xs.
  Proof.
    intros p a xs.
    induction xs as [| [q b] xs IH]; simpl; intros H; try discriminate.
    destruct (Nat.eqb p q) eqn:Hpq.
    - inversion H; subst b.
      apply Nat.eqb_eq in Hpq. subst q.
      now left.
    - right. now apply IH.
  Qed.

  Lemma atoms_key_in_positions :
    forall (r : positioned_regex A) p a,
      In (p, a) (atoms r) ->
      In p (positions r).
  Proof.
    intros r p a Hin.
    rewrite <- atoms_positions.
    change p with (fst (p, a)).
    now apply in_map.
  Qed.

  Lemma label_of_sound :
    forall (r : positioned_regex A) p a,
      label_of r p = Some a ->
      In (p, a) (atoms r).
  Proof.
    intros r p a H.
    unfold label_of in H.
    now apply lookup_symbol_key_in.
  Qed.

  Lemma run_from_marked_in_atoms :
    forall (r : positioned_regex A) p mw,
      run_from_marked (followpos r) (label_of r) p mw ->
      Forall (fun pa => In pa (atoms r)) mw.
  Proof.
    intros r p mw.
    revert p.
    induction mw as [| [q a] mw IH]; intros p Hrun; simpl in *.
    - constructor.
    - destruct Hrun as [_ [Hlbl Hrun]].
      constructor.
      + now apply label_of_sound.
      + now apply IH with (p := q).
  Qed.

  Lemma accepts_marked_in_atoms :
    forall (r : positioned_regex A) mw,
      accepts_marked r mw ->
      Forall (fun pa => In pa (atoms r)) mw.
  Proof.
    intros r mw Hacc.
    destruct mw as [| [p a] mw].
    - constructor.
    - simpl in Hacc.
      destruct Hacc as [_ [Hlbl [Hrun _]]].
      constructor.
      + now apply label_of_sound.
      + now apply run_from_marked_in_atoms with (p := p).
  Qed.

  Lemma accepts_marked_empty_matches_marked :
    forall (r : positioned_regex A),
      accepts_marked r [] ->
      matches_marked r [].
  Proof.
    intros r Hacc.
    simpl in Hacc.
    now apply nullable_matches_marked.
  Qed.

  Lemma run_from_marked_empty_table_nil :
    forall (lbl : symbol_at) p (mw : list (nat * A)),
      run_from_marked [] lbl p mw ->
      mw = [].
  Proof.
    intros lbl p mw.
    destruct mw as [| [q a] mw]; simpl; intros Hrun; auto.
    destruct Hrun as [Hmem _]. discriminate.
  Qed.

  Lemma accepts_marked_atom_matches_marked :
    forall p (a : A) (mw : list (nat * A)),
      accepts_marked (PAtom p a) mw ->
      matches_marked (PAtom p a) mw.
  Proof.
    intros p a mw Hacc.
    destruct mw as [| [q b] mw].
    - simpl in Hacc. discriminate.
    - simpl in Hacc.
      destruct Hacc as [Hfirst [Hlbl [Hrun _]]].
      simpl in Hfirst.
      apply Bool.orb_true_iff in Hfirst as [Hfirst | Hfirst]; [| discriminate].
      apply Nat.eqb_eq in Hfirst. subst q.
      unfold label_of in Hlbl. simpl in Hlbl.
      rewrite Nat.eqb_refl in Hlbl.
      inversion Hlbl; subst b.
      apply run_from_marked_empty_table_nil in Hrun. subst mw.
      constructor.
  Qed.

  Lemma label_of_app_right_preserve :
    forall (r1 r2 : positioned_regex A) p a,
      NoDup (positions r1 ++ positions r2) ->
      label_of r2 p = Some a ->
      lookup_symbol p (atoms r1 ++ atoms r2) = Some a.
  Proof.
    intros r1 r2 p a Hnodup Hlbl.
    unfold label_of in Hlbl.
    rewrite lookup_symbol_app_right.
    - exact Hlbl.
    - intros b Hin.
      pose proof (lookup_symbol_key_in p a (atoms r2) Hlbl) as Hin2_atom.
      pose proof (atoms_key_in_positions r1 p b Hin) as Hin1.
      pose proof (atoms_key_in_positions r2 p a Hin2_atom) as Hin2.
      eapply NoDup_app_not_both; eauto.
  Qed.

  Lemma label_of_app_left_reflect :
    forall (r1 r2 : positioned_regex A) p a,
      NoDup (positions r1 ++ positions r2) ->
      In p (positions r1) ->
      lookup_symbol p (atoms r1 ++ atoms r2) = Some a ->
      label_of r1 p = Some a.
  Proof.
    intros r1 r2 p a Hnodup Hpin Hlbl.
    unfold label_of.
    destruct (lookup_symbol p (atoms r1)) as [a1|] eqn:Hleft.
    - unfold label_of in Hlbl.
      rewrite (lookup_symbol_app_left p a1 (atoms r1) (atoms r2) Hleft) in Hlbl.
      now inversion Hlbl.
    - exfalso.
      rewrite <- atoms_positions in Hpin.
      apply in_map_iff in Hpin as [[q b] [Hp Hin]].
      simpl in Hp. subst q.
      pose proof (NoDup_app_left _ _ Hnodup) as Hnodup1.
      pose proof (label_of_complete r1 p b Hnodup1 Hin) as Hcomplete.
      unfold label_of in Hcomplete.
      rewrite Hleft in Hcomplete. discriminate.
  Qed.

  Lemma label_of_app_right_reflect :
    forall (r1 r2 : positioned_regex A) p a,
      NoDup (positions r1 ++ positions r2) ->
      In p (positions r2) ->
      lookup_symbol p (atoms r1 ++ atoms r2) = Some a ->
      label_of r2 p = Some a.
  Proof.
    intros r1 r2 p a Hnodup Hpin Hlbl.
    unfold label_of.
    rewrite lookup_symbol_app_right in Hlbl.
    - exact Hlbl.
    - intros b Hin.
      pose proof (atoms_key_in_positions r1 p b Hin) as Hin1.
      eapply NoDup_app_not_both; eauto.
  Qed.

  Lemma label_of_alt_left_preserve :
    forall (r1 r2 : positioned_regex A) p a,
      label_of r1 p = Some a ->
      label_of (PAlt r1 r2) p = Some a.
  Proof.
    intros r1 r2 p a H.
    unfold label_of in *. simpl.
    now apply lookup_symbol_app_left.
  Qed.

  Lemma label_of_alt_left_reflect :
    forall (r1 r2 : positioned_regex A) p a,
      NoDup (positions (PAlt r1 r2)) ->
      In p (positions r1) ->
      label_of (PAlt r1 r2) p = Some a ->
      label_of r1 p = Some a.
  Proof.
    intros r1 r2 p a Hnodup Hpin Hlbl.
    unfold label_of in Hlbl. simpl in Hlbl.
    eapply label_of_app_left_reflect; eauto.
  Qed.

  Lemma label_of_alt_right_preserve :
    forall (r1 r2 : positioned_regex A) p a,
      NoDup (positions (PAlt r1 r2)) ->
      label_of r2 p = Some a ->
      label_of (PAlt r1 r2) p = Some a.
  Proof.
    intros r1 r2 p a Hnodup H.
    unfold label_of. simpl.
    eapply label_of_app_right_preserve; eauto.
  Qed.

  Lemma label_of_alt_right_reflect :
    forall (r1 r2 : positioned_regex A) p a,
      NoDup (positions (PAlt r1 r2)) ->
      In p (positions r2) ->
      label_of (PAlt r1 r2) p = Some a ->
      label_of r2 p = Some a.
  Proof.
    intros r1 r2 p a Hnodup Hpin Hlbl.
    unfold label_of in Hlbl. simpl in Hlbl.
    eapply label_of_app_right_reflect; eauto.
  Qed.

  Lemma label_of_cat_left_preserve :
    forall (r1 r2 : positioned_regex A) p a,
      label_of r1 p = Some a ->
      label_of (PCat r1 r2) p = Some a.
  Proof.
    intros r1 r2 p a H.
    unfold label_of in *. simpl.
    now apply lookup_symbol_app_left.
  Qed.

  Lemma label_of_cat_left_reflect :
    forall (r1 r2 : positioned_regex A) p a,
      NoDup (positions (PCat r1 r2)) ->
      In p (positions r1) ->
      label_of (PCat r1 r2) p = Some a ->
      label_of r1 p = Some a.
  Proof.
    intros r1 r2 p a Hnodup Hpin Hlbl.
    unfold label_of in Hlbl. simpl in Hlbl.
    eapply label_of_app_left_reflect; eauto.
  Qed.

  Lemma label_of_cat_right_preserve :
    forall (r1 r2 : positioned_regex A) p a,
      NoDup (positions (PCat r1 r2)) ->
      label_of r2 p = Some a ->
      label_of (PCat r1 r2) p = Some a.
  Proof.
    intros r1 r2 p a Hnodup H.
    unfold label_of. simpl.
    eapply label_of_app_right_preserve; eauto.
  Qed.

  Lemma label_of_cat_right_reflect :
    forall (r1 r2 : positioned_regex A) p a,
      NoDup (positions (PCat r1 r2)) ->
      In p (positions r2) ->
      label_of (PCat r1 r2) p = Some a ->
      label_of r2 p = Some a.
  Proof.
    intros r1 r2 p a Hnodup Hpin Hlbl.
    unfold label_of in Hlbl. simpl in Hlbl.
    eapply label_of_app_right_reflect; eauto.
  Qed.

  Lemma label_of_star_preserve :
    forall (r : positioned_regex A) p a,
      label_of r p = Some a ->
      label_of (PStar r) p = Some a.
  Proof.
    auto.
  Qed.

  Lemma run_from_marked_preserve :
    forall
      (tbl1 tbl2 : follow_table)
      (lbl1 lbl2 : symbol_at)
      p
      (mw : list (nat * A)),
      (forall x y,
          mem y (lookup_follow x tbl1) = true ->
          mem y (lookup_follow x tbl2) = true) ->
      (forall x a, lbl1 x = Some a -> lbl2 x = Some a) ->
      run_from_marked tbl1 lbl1 p mw ->
      run_from_marked tbl2 lbl2 p mw.
  Proof.
    intros tbl1 tbl2 lbl1 lbl2 p mw Hfollow Hlabel.
    revert p.
    induction mw as [| [q a] mw IH]; intros p Hrun; simpl in *; auto.
    destruct Hrun as [Hedge [Hlbl Hrun]].
    repeat split; auto.
  Qed.

  Lemma run_from_marked_alt_left_reflect :
    forall (r1 r2 : positioned_regex A) p (mw : list (nat * A)),
      NoDup (positions (PAlt r1 r2)) ->
      In p (positions r1) ->
      run_from_marked (followpos (PAlt r1 r2)) (label_of (PAlt r1 r2)) p mw ->
      run_from_marked (followpos r1) (label_of r1) p mw.
  Proof.
    intros r1 r2 p mw Hnodup Hpin Hrun.
    revert p Hpin Hrun.
    induction mw as [| [q a] mw IH]; intros p Hpin Hrun; simpl in *; auto.
    destruct Hrun as [Hedge [Hlbl Hrun]].
    pose proof (lookup_follow_app_left_reflect r1 r2 p q Hnodup Hpin Hedge)
      as Hedge1.
    pose proof (mem_lookup_follow_value_in_positions r1 p q Hedge1)
      as Hqin.
    repeat split.
    - exact Hedge1.
    - eapply label_of_alt_left_reflect; eauto.
    - eapply IH; eauto.
  Qed.

  Lemma run_from_marked_alt_right_reflect :
    forall (r1 r2 : positioned_regex A) p (mw : list (nat * A)),
      NoDup (positions (PAlt r1 r2)) ->
      In p (positions r2) ->
      run_from_marked (followpos (PAlt r1 r2)) (label_of (PAlt r1 r2)) p mw ->
      run_from_marked (followpos r2) (label_of r2) p mw.
  Proof.
    intros r1 r2 p mw Hnodup Hpin Hrun.
    revert p Hpin Hrun.
    induction mw as [| [q a] mw IH]; intros p Hpin Hrun; simpl in *; auto.
    destruct Hrun as [Hedge [Hlbl Hrun]].
    pose proof (lookup_follow_app_right_reflect r1 r2 p q Hnodup Hpin Hedge)
      as Hedge2.
    pose proof (mem_lookup_follow_value_in_positions r2 p q Hedge2)
      as Hqin.
    repeat split.
    - exact Hedge2.
    - eapply label_of_alt_right_reflect; eauto.
    - eapply IH; eauto.
  Qed.

  Lemma run_from_marked_last_position_in_positions :
    forall (r : positioned_regex A) p mw,
      In p (positions r) ->
      run_from_marked (followpos r) (label_of r) p mw ->
      In (last_position_from p mw) (positions r).
  Proof.
    intros r p mw.
    revert p.
    induction mw as [| [q a] mw IH]; intros p Hpin Hrun; simpl in *.
    - exact Hpin.
    - destruct Hrun as [Hedge [_ Hrun]].
      apply IH; auto.
      eapply mem_lookup_follow_value_in_positions; eauto.
  Qed.

  Lemma mem_lastpos_alt_left_reflect :
    forall (r1 r2 : positioned_regex A) p,
      NoDup (positions (PAlt r1 r2)) ->
      In p (positions r1) ->
      mem p (lastpos (PAlt r1 r2)) = true ->
      mem p (lastpos r1) = true.
  Proof.
    intros r1 r2 p Hnodup Hpin Hmem.
    simpl in Hmem.
    apply mem_union_elim in Hmem as [Hmem | Hmem]; auto.
    exfalso.
    apply mem_true_In in Hmem.
    pose proof (lastpos_In_positions r2 p Hmem) as Hpin2.
    eapply NoDup_app_not_both; eauto.
  Qed.

  Lemma mem_lastpos_alt_right_reflect :
    forall (r1 r2 : positioned_regex A) p,
      NoDup (positions (PAlt r1 r2)) ->
      In p (positions r2) ->
      mem p (lastpos (PAlt r1 r2)) = true ->
      mem p (lastpos r2) = true.
  Proof.
    intros r1 r2 p Hnodup Hpin Hmem.
    simpl in Hmem.
    apply mem_union_elim in Hmem as [Hmem | Hmem]; auto.
    exfalso.
    apply mem_true_In in Hmem.
    pose proof (lastpos_In_positions r1 p Hmem) as Hpin1.
    eapply NoDup_app_not_both; eauto.
  Qed.

  Lemma lookup_follow_add_follow_neq :
    forall p x xs t,
      p <> x ->
      lookup_follow p (add_follow x xs t) = lookup_follow p t.
  Proof.
    intros p x xs t Hneq.
    induction t as [| [y ys] t IH]; simpl.
    - destruct (Nat.eqb p x) eqn:Hpx; auto.
      apply Nat.eqb_eq in Hpx. contradiction.
    - destruct (Nat.eqb x y) eqn:Hxy; simpl.
      + destruct (Nat.eqb p y) eqn:Hpy; auto.
        apply Nat.eqb_eq in Hxy.
        apply Nat.eqb_eq in Hpy.
        subst. contradiction.
      + destruct (Nat.eqb p y); auto.
  Qed.

  Lemma lookup_follow_add_follow_all_not_from :
    forall p from to_ t,
      ~ In p from ->
      lookup_follow p (add_follow_all from to_ t) = lookup_follow p t.
  Proof.
    intros p from.
    induction from as [| x from IH]; simpl; intros to_ t Hnotin.
    - reflexivity.
    - rewrite IH.
      + apply lookup_follow_add_follow_neq.
        intro Heq. subst x. apply Hnotin. now left.
      + intros Hin. apply Hnotin. now right.
  Qed.

  Lemma lookup_follow_add_follow_elim :
    forall p q x xs t,
      mem q (lookup_follow p (add_follow x xs t)) = true ->
      mem q (lookup_follow p t) = true \/
        (p = x /\ mem q xs = true).
  Proof.
    intros p q x xs t.
    induction t as [| [y ys] t IH]; simpl; intros H.
    - destruct (Nat.eqb p x) eqn:Hpx; try discriminate.
      apply Nat.eqb_eq in Hpx. subst x.
      right. split; auto.
    - destruct (Nat.eqb x y) eqn:Hxy; simpl in H.
      + destruct (Nat.eqb p y) eqn:Hpy.
        * apply Nat.eqb_eq in Hxy.
          apply Nat.eqb_eq in Hpy.
          subst x y.
          apply mem_union_elim in H as [H | H].
          -- right. split; auto.
          -- left. simpl. exact H.
        * left. simpl. exact H.
      + destruct (Nat.eqb p y) eqn:Hpy.
        * left. simpl. exact H.
        * destruct (IH H) as [Hbase | [Heq Hxs]].
          -- left. simpl. exact Hbase.
          -- right. split; auto.
  Qed.

  Lemma lookup_follow_add_follow_all_elim :
    forall p q from to_ t,
      mem q (lookup_follow p (add_follow_all from to_ t)) = true ->
      mem q (lookup_follow p t) = true \/
        (mem p from = true /\ mem q to_ = true).
  Proof.
    intros p q from.
    induction from as [| x from IH]; simpl; intros to_ t H.
    - now left.
    - destruct (IH to_ (add_follow x to_ t) H) as [Hadd | [Hfrom Hto]].
      + destruct (lookup_follow_add_follow_elim p q x to_ t Hadd)
          as [Hbase | [Heq Hto]].
        * now left.
        * right. split; auto.
          subst x. simpl. rewrite Nat.eqb_refl. reflexivity.
      + right. split; auto.
        simpl. apply Bool.orb_true_iff. now right.
  Qed.

  Lemma firstpos_cat_elim :
    forall (r1 r2 : positioned_regex A) p,
      mem p (firstpos (PCat r1 r2)) = true ->
      mem p (firstpos r1) = true \/
        (nullable r1 = true /\ mem p (firstpos r2) = true).
  Proof.
    intros r1 r2 p Hmem.
    simpl in Hmem.
    destruct (nullable r1) eqn:Hnull.
    - apply mem_union_elim in Hmem as [Hmem | Hmem]; auto.
    - now left.
  Qed.

  Lemma mem_lastpos_cat_left_reflect :
    forall (r1 r2 : positioned_regex A) p,
      NoDup (positions (PCat r1 r2)) ->
      In p (positions r1) ->
      mem p (lastpos (PCat r1 r2)) = true ->
      nullable r2 = true /\ mem p (lastpos r1) = true.
  Proof.
    intros r1 r2 p Hnodup Hpin Hmem.
    simpl in Hmem.
    destruct (nullable r2) eqn:Hnull.
    - split; auto.
      apply mem_union_elim in Hmem as [Hmem | Hmem]; auto.
      exfalso.
      apply mem_true_In in Hmem.
      pose proof (lastpos_In_positions r2 p Hmem) as Hpin2.
      eapply NoDup_app_not_both; eauto.
    - exfalso.
      apply mem_true_In in Hmem.
      pose proof (lastpos_In_positions r2 p Hmem) as Hpin2.
      eapply NoDup_app_not_both; eauto.
  Qed.

  Lemma mem_lastpos_cat_right_reflect :
    forall (r1 r2 : positioned_regex A) p,
      NoDup (positions (PCat r1 r2)) ->
      In p (positions r2) ->
      mem p (lastpos (PCat r1 r2)) = true ->
      mem p (lastpos r2) = true.
  Proof.
    intros r1 r2 p Hnodup Hpin Hmem.
    simpl in Hmem.
    destruct (nullable r2) eqn:Hnull.
    - apply mem_union_elim in Hmem as [Hmem | Hmem]; auto.
      exfalso.
      apply mem_true_In in Hmem.
      pose proof (lastpos_In_positions r1 p Hmem) as Hpin1.
      eapply NoDup_app_not_both; eauto.
    - exact Hmem.
  Qed.

  Lemma label_of_cat_position_elim :
    forall (r1 r2 : positioned_regex A) p a,
      label_of (PCat r1 r2) p = Some a ->
      In p (positions r1) \/ In p (positions r2).
  Proof.
    intros r1 r2 p a Hlbl.
    apply label_of_sound in Hlbl.
    simpl in Hlbl.
    apply in_app_iff in Hlbl as [Hin | Hin].
    - left. eapply atoms_key_in_positions; eauto.
    - right. eapply atoms_key_in_positions; eauto.
  Qed.

  Lemma lookup_follow_cat_left_to_left_reflect :
    forall (r1 r2 : positioned_regex A) p q,
      NoDup (positions (PCat r1 r2)) ->
      In p (positions r1) ->
      In q (positions r1) ->
      mem q (lookup_follow p (followpos (PCat r1 r2))) = true ->
      mem q (lookup_follow p (followpos r1)) = true.
  Proof.
    intros r1 r2 p q Hnodup Hpin Hqin Hedge.
    simpl in Hedge.
    apply lookup_follow_add_follow_all_elim in Hedge
      as [Hbase | [Hlast Hfirst]].
    - eapply lookup_follow_app_left_reflect; eauto.
    - exfalso.
      apply mem_true_In in Hfirst.
      pose proof (firstpos_In_positions r2 q Hfirst) as Hqin2.
      eapply NoDup_app_not_both; eauto.
  Qed.

  Lemma lookup_follow_cat_boundary_reflect :
    forall (r1 r2 : positioned_regex A) p q,
      NoDup (positions (PCat r1 r2)) ->
      In p (positions r1) ->
      In q (positions r2) ->
      mem q (lookup_follow p (followpos (PCat r1 r2))) = true ->
      mem p (lastpos r1) = true /\ mem q (firstpos r2) = true.
  Proof.
    intros r1 r2 p q Hnodup Hpin Hqin Hedge.
    simpl in Hedge.
    apply lookup_follow_add_follow_all_elim in Hedge
      as [Hbase | Hboundary]; auto.
    exfalso.
    pose proof (lookup_follow_app_left_reflect r1 r2 p q Hnodup Hpin Hbase)
      as Hedge1.
    pose proof (mem_lookup_follow_value_in_positions r1 p q Hedge1)
      as Hqin1.
    eapply NoDup_app_not_both; eauto.
  Qed.

  Lemma run_from_marked_cat_right_reflect :
    forall (r1 r2 : positioned_regex A) p (mw : list (nat * A)),
      NoDup (positions (PCat r1 r2)) ->
      In p (positions r2) ->
      run_from_marked (followpos (PCat r1 r2)) (label_of (PCat r1 r2)) p mw ->
      run_from_marked (followpos r2) (label_of r2) p mw.
  Proof.
    intros r1 r2 p mw Hnodup Hpin Hrun.
    revert p Hpin Hrun.
    induction mw as [| [q a] mw IH]; intros p Hpin Hrun; simpl in *; auto.
    destruct Hrun as [Hedge [Hlbl Hrun]].
    simpl in Hedge.
    rewrite lookup_follow_add_follow_all_not_from in Hedge.
    - pose proof (lookup_follow_app_right_reflect r1 r2 p q Hnodup Hpin Hedge)
        as Hedge2.
      pose proof (mem_lookup_follow_value_in_positions r2 p q Hedge2)
        as Hqin.
      repeat split.
      + exact Hedge2.
      + eapply label_of_cat_right_reflect; eauto.
      + eapply IH; eauto.
    - intros Hlast.
      pose proof (lastpos_In_positions r1 p Hlast) as Hpin1.
      eapply NoDup_app_not_both; eauto.
  Qed.

  Lemma run_from_marked_cat_left_split :
    forall (r1 r2 : positioned_regex A) p (mw : list (nat * A)),
      NoDup (positions (PCat r1 r2)) ->
      In p (positions r1) ->
      run_from_marked (followpos (PCat r1 r2)) (label_of (PCat r1 r2)) p mw ->
      (run_from_marked (followpos r1) (label_of r1) p mw /\
        In (last_position_from p mw) (positions r1)) \/
      exists prefix q b suffix,
        mw = prefix ++ (q, b) :: suffix /\
        run_from_marked (followpos r1) (label_of r1) p prefix /\
        mem (last_position_from p prefix) (lastpos r1) = true /\
        mem q (firstpos r2) = true /\
        label_of r2 q = Some b /\
        run_from_marked (followpos r2) (label_of r2) q suffix.
  Proof.
    intros r1 r2 p mw Hnodup Hpin Hrun.
    revert p Hpin Hrun.
    induction mw as [| [q b] mw IH]; intros p Hpin Hrun; simpl in *.
    - left. split; auto.
    - destruct Hrun as [Hedge [Hlbl Hrun]].
      destruct (label_of_cat_position_elim r1 r2 q b Hlbl)
        as [Hqin1 | Hqin2].
      + pose proof
          (lookup_follow_cat_left_to_left_reflect
             r1 r2 p q Hnodup Hpin Hqin1 Hedge)
          as Hedge1.
        pose proof
          (label_of_cat_left_reflect r1 r2 q b Hnodup Hqin1 Hlbl)
          as Hlbl1.
        destruct (IH q Hqin1 Hrun)
          as [[Hrun1 Hlastin] |
              [prefix [x [c [suffix
                [Heq [Hrun_prefix [Hlast [Hfirst [Hlbl2 Hrun2]]]]]]]]]].
        * left. split.
          -- repeat split; assumption.
          -- exact Hlastin.
        * right.
          exists ((q, b) :: prefix), x, c, suffix.
          split.
          -- simpl. now rewrite Heq.
          -- repeat split; auto.
      + pose proof
          (lookup_follow_cat_boundary_reflect
             r1 r2 p q Hnodup Hpin Hqin2 Hedge)
          as [Hlast Hfirst].
        pose proof
          (label_of_cat_right_reflect r1 r2 q b Hnodup Hqin2 Hlbl)
          as Hlbl2.
        pose proof
          (run_from_marked_cat_right_reflect r1 r2 q mw Hnodup Hqin2 Hrun)
          as Hrun2.
        right.
        exists [], q, b, mw.
        simpl. repeat split; auto.
  Qed.

  Lemma lookup_follow_star_elim :
    forall (r : positioned_regex A) p q,
      mem q (lookup_follow p (followpos (PStar r))) = true ->
      mem q (lookup_follow p (followpos r)) = true \/
        (mem p (lastpos r) = true /\ mem q (firstpos r) = true).
  Proof.
    intros r p q Hedge.
    simpl in Hedge.
    now apply lookup_follow_add_follow_all_elim in Hedge.
  Qed.

  Lemma run_from_marked_star_split :
    forall (r : positioned_regex A) p (mw : list (nat * A)),
      In p (positions r) ->
      run_from_marked (followpos (PStar r)) (label_of (PStar r)) p mw ->
      (run_from_marked (followpos r) (label_of r) p mw /\
        In (last_position_from p mw) (positions r)) \/
      exists prefix q b suffix,
        mw = prefix ++ (q, b) :: suffix /\
        run_from_marked (followpos r) (label_of r) p prefix /\
        mem (last_position_from p prefix) (lastpos r) = true /\
        mem q (firstpos r) = true /\
        label_of r q = Some b /\
        run_from_marked (followpos (PStar r)) (label_of (PStar r)) q suffix.
  Proof.
    intros r p mw Hpin Hrun.
    revert p Hpin Hrun.
    induction mw as [| [q b] mw IH]; intros p Hpin Hrun; simpl in *.
    - left. split; auto.
    - destruct Hrun as [Hedge [Hlbl Hrun]].
      simpl in Hlbl.
      destruct (lookup_follow_star_elim r p q Hedge)
        as [Hbase | [Hlast Hfirst]].
      + pose proof (mem_lookup_follow_value_in_positions r p q Hbase)
          as Hqin.
        destruct (IH q Hqin Hrun)
          as [[Hrun_r Hlastin] |
              [prefix [x [c [suffix
                [Heq [Hrun_prefix [Hlast1 [Hfirst2 [Hlbl2 Hrun2]]]]]]]]]].
        * left. split.
          -- repeat split; assumption.
          -- exact Hlastin.
        * right.
          exists ((q, b) :: prefix), x, c, suffix.
          split.
          -- simpl. now rewrite Heq.
          -- repeat split; auto.
      + right.
        exists [], q, b, mw.
        simpl. repeat split; auto.
  Qed.

  Lemma run_from_marked_app_cons :
    forall tbl lbl p xs q b ys,
      run_from_marked tbl lbl p xs ->
      mem q (lookup_follow (last_position_from p xs) tbl) = true ->
      lbl q = Some b ->
      run_from_marked tbl lbl q ys ->
      run_from_marked tbl lbl p (xs ++ (q, b) :: ys).
  Proof.
    intros tbl lbl p xs.
    revert p.
    induction xs as [| [r c] xs IH]; intros p q b ys Hrun Hedge Hlbl Htail.
    - simpl in *. repeat split; assumption.
    - simpl in *.
      destruct Hrun as [Hedge0 [Hlbl0 Hrun]].
      split; [exact Hedge0 |].
      split; [exact Hlbl0 |].
      eapply IH; eauto.
  Qed.

  Theorem matches_marked_run_from_marked :
    forall (pr : positioned_regex A) mw,
      NoDup (positions pr) ->
      matches_marked pr mw ->
      forall p a rest,
        mw = (p, a) :: rest ->
        run_from_marked (followpos pr) (label_of pr) p rest.
  Proof.
    intros pr mw Hnodup Hm.
    induction Hm; intros p0 a0 rest Heq; simpl in *; try discriminate.
    - inversion Heq; subst. constructor.
    - eapply run_from_marked_preserve.
      + intros x y Hxy. eapply followpos_alt_left_preserve; exact Hxy.
      + intros x b Hlbl. eapply label_of_alt_left_preserve; exact Hlbl.
      + eapply IHHm; eauto.
        apply NoDup_app_left in Hnodup. exact Hnodup.
    - eapply run_from_marked_preserve.
      + intros x y Hxy. eapply followpos_alt_right_preserve; eauto.
      + intros x b Hlbl. eapply label_of_alt_right_preserve; eauto.
      + eapply IHHm; eauto.
        apply NoDup_app_right in Hnodup. exact Hnodup.
    - destruct mw1 as [| [p1 a1] mw1'].
      + simpl in Heq. inversion Heq; subst.
        eapply run_from_marked_preserve.
        * intros x y Hxy. eapply followpos_cat_right_preserve; eauto.
        * intros x b Hlbl. eapply label_of_cat_right_preserve; eauto.
        * eapply IHHm2; eauto.
          apply NoDup_app_right in Hnodup. exact Hnodup.
      + destruct mw2 as [| [q b] mw2'].
        * rewrite app_nil_r in Heq.
          inversion Heq; subst.
          eapply run_from_marked_preserve.
          -- intros x y Hxy. eapply followpos_cat_left_preserve; exact Hxy.
          -- intros x c Hlbl. eapply label_of_cat_left_preserve; exact Hlbl.
          -- eapply IHHm1; eauto.
             apply NoDup_app_left in Hnodup. exact Hnodup.
        * inversion Heq; subst.
          eapply run_from_marked_app_cons.
          -- eapply run_from_marked_preserve.
             ++ intros x y Hxy. eapply followpos_cat_left_preserve; exact Hxy.
             ++ intros x c Hlbl. eapply label_of_cat_left_preserve; exact Hlbl.
             ++ eapply IHHm1; eauto.
                apply NoDup_app_left in Hnodup. exact Hnodup.
          -- apply followpos_cat_boundary.
             ++ eapply matches_marked_lastpos; eauto.
             ++ eapply matches_marked_firstpos; eauto.
          -- eapply label_of_cat_right_preserve; eauto.
             eapply matches_marked_head_label.
             ++ apply NoDup_app_right in Hnodup. exact Hnodup.
             ++ exact Hm2.
          -- eapply run_from_marked_preserve.
             ++ intros x y Hxy. eapply followpos_cat_right_preserve; eauto.
             ++ intros x c Hlbl. eapply label_of_cat_right_preserve; eauto.
             ++ eapply IHHm2; eauto.
                apply NoDup_app_right in Hnodup. exact Hnodup.
    - destruct mw1 as [| [p1 a1] mw1']; [contradiction |].
      destruct mw2 as [| [q b] mw2'].
      + rewrite app_nil_r in Heq.
        inversion Heq; subst.
        eapply run_from_marked_preserve.
        * intros x y Hxy. eapply followpos_star_preserve; exact Hxy.
        * intros x c Hlbl. eapply label_of_star_preserve; exact Hlbl.
        * eapply IHHm1; eauto.
      + inversion Heq; subst.
        eapply run_from_marked_app_cons.
        * eapply run_from_marked_preserve.
          -- intros x y Hxy. eapply followpos_star_preserve; exact Hxy.
          -- intros x c Hlbl. eapply label_of_star_preserve; exact Hlbl.
          -- eapply IHHm1; eauto.
        * apply followpos_star_boundary.
          -- eapply matches_marked_lastpos
               with (pr := r) (mw := (p0, a0) :: mw1')
                    (p := p0) (a := a0) (rest := mw1').
             ++ exact Hm1.
             ++ reflexivity.
          -- eapply matches_marked_firstpos
               with (pr := PStar r) (mw := (q, b) :: mw2')
                    (p := q) (a := b) (rest := mw2').
             ++ exact Hm2.
             ++ reflexivity.
        * eapply matches_marked_head_label; eauto.
        * eapply IHHm2; eauto.
  Qed.

  Lemma mem_matching_positions :
    forall
      (label_matches : A -> A -> bool)
      (lbl : symbol_at)
      ps p a,
      (forall x, label_matches x x = true) ->
      mem p ps = true ->
      lbl p = Some a ->
      In (Some p) (matching_positions label_matches lbl ps a).
  Proof.
    intros label_matches lbl ps.
    induction ps as [| q ps IH]; simpl; intros p a Hrefl Hmem Hlbl.
    - discriminate.
    - apply Bool.orb_true_iff in Hmem as [Heq | Hmem].
      + apply Nat.eqb_eq in Heq. subst q.
        rewrite Hlbl, Hrefl. simpl. auto.
      + destruct (lbl q) as [b|] eqn:Hq.
        * destruct (label_matches b a); simpl; auto.
        * auto.
  Qed.

  Lemma matching_positions_in_state :
    forall
      (label_matches : A -> A -> bool)
      (lbl : symbol_at)
      ps a s,
      In s (matching_positions label_matches lbl ps a) ->
      exists p b,
        s = Some p /\
        mem p ps = true /\
        lbl p = Some b /\
        label_matches b a = true.
  Proof.
    intros label_matches lbl ps.
    induction ps as [| p ps IH]; simpl; intros a s Hin.
    - contradiction.
    - destruct (lbl p) as [b|] eqn:Hlbl.
      + destruct (label_matches b a) eqn:Hmatch.
        * simpl in Hin. destruct Hin as [Heq | Hin].
          -- subst s. exists p, b. repeat split; auto.
             simpl. rewrite Nat.eqb_refl. reflexivity.
          -- destruct (IH a s Hin) as [q [c [Hs [Hmem [Hlblq Hmatchq]]]]].
             exists q, c. repeat split; auto.
             simpl. apply Bool.orb_true_iff. now right.
        * destruct (IH a s Hin) as [q [c [Hs [Hmem [Hlblq Hmatchq]]]]].
          exists q, c. repeat split; auto.
          simpl. apply Bool.orb_true_iff. now right.
      + destruct (IH a s Hin) as [q [c [Hs [Hmem [Hlblq Hmatchq]]]]].
        exists q, c. repeat split; auto.
        simpl. apply Bool.orb_true_iff. now right.
  Qed.

  Lemma position_nfa_path_from_position_accepts_tail :
    forall
      (label_matches : A -> A -> bool)
      (r : positioned_regex A)
      p w s,
      (forall x y, label_matches x y = true -> x = y) ->
      path_from (position_nfa label_matches r) (Some p) w s ->
      position_nfa_final r s = true ->
      exists mw,
        symbols mw = w /\
        run_from_marked (followpos r) (label_of r) p mw /\
        mem (last_position_from p mw) (lastpos r) = true.
  Proof.
    intros label_matches r p w.
    revert p.
    induction w as [| a w IH]; intros p s Hsound Hpath Hfinal.
    - inversion Hpath; subst.
      exists []. simpl. repeat split; exact Hfinal || constructor.
    - inversion Hpath as [| st a' st' w' s' Hstep Htail]; subst.
      unfold position_nfa in Hstep. simpl in Hstep.
      destruct (matching_positions_in_state _ _ _ _ _ Hstep)
        as [q [b [Hst' [Hfollow [Hlbl Hmatch]]]]].
      subst st'.
      apply Hsound in Hmatch. subst b.
      destruct (IH q s Hsound Htail Hfinal)
        as [mw [Hsym [Hrun Hlast]]].
      exists ((q, a) :: mw). simpl.
      split; [now rewrite Hsym |].
      split.
      + repeat split; assumption.
      + exact Hlast.
  Qed.

  Lemma rev_last_position_from :
    forall mw p a,
      match List.rev ((p, a) :: mw) with
      | [] => False
      | (q, _) :: _ => q = last_position_from p mw
      end.
  Proof.
    induction mw as [| [q b] mw IH]; intros p a; simpl.
    - reflexivity.
    - specialize (IH q b).
      destruct (List.rev ((q, b) :: mw)) as [| [r c] rest] eqn:Hrev.
      + pose proof (f_equal (@length (nat * A)) Hrev) as Hlen.
        rewrite length_rev in Hlen. simpl in Hlen. lia.
      + change (List.rev mw ++ [(q, b)]) with (List.rev ((q, b) :: mw)).
        rewrite Hrev. simpl. simpl in IH. exact IH.
  Qed.

  Lemma rev_last_position_from_mem :
    forall mw p a ps,
      match List.rev ((p, a) :: mw) with
      | [] => False
      | (q, _) :: _ => mem q ps = true
      end ->
      mem (last_position_from p mw) ps = true.
  Proof.
    intros mw p a ps Hmem.
    pose proof (rev_last_position_from mw p a) as Hlast.
    destruct (List.rev ((p, a) :: mw)) as [| [q b] rest]; try contradiction.
    simpl in Hlast. subst q.
    exact Hmem.
  Qed.

  Lemma last_position_from_rev_mem :
    forall mw p a ps,
      mem (last_position_from p mw) ps = true ->
      match List.rev ((p, a) :: mw) with
      | [] => False
      | (q, _) :: _ => mem q ps = true
      end.
  Proof.
    intros mw p a ps Hmem.
    pose proof (rev_last_position_from mw p a) as Hlast.
    destruct (List.rev ((p, a) :: mw)) as [| [q b] rest]; try contradiction.
    simpl in Hlast. subst q.
    exact Hmem.
  Qed.

  Lemma accepts_marked_cat_matches_marked :
    forall (r1 r2 : positioned_regex A) mw,
      NoDup (positions (PCat r1 r2)) ->
      (forall mw, accepts_marked r1 mw -> matches_marked r1 mw) ->
      (forall mw, accepts_marked r2 mw -> matches_marked r2 mw) ->
      accepts_marked (PCat r1 r2) mw ->
      matches_marked (PCat r1 r2) mw.
  Proof.
    intros r1 r2 mw Hnodup IH1 IH2 Hacc.
    destruct mw as [| [p a] rest].
    - simpl in Hacc.
      apply Bool.andb_true_iff in Hacc as [Hnull1 Hnull2].
      change (matches_marked (PCat r1 r2)
        (([] : list (nat * A)) ++ ([] : list (nat * A)))).
      apply MM_Cat; [apply IH1 | apply IH2]; simpl; assumption.
    - simpl in Hacc.
      destruct Hacc as [Hfirst [Hlbl [Hrun Hlast_rev]]].
      pose proof
        (rev_last_position_from_mem
           rest p a (lastpos (PCat r1 r2)) Hlast_rev)
        as Hlast_cat.
      destruct (firstpos_cat_elim r1 r2 p Hfirst)
        as [Hfirst1 | [Hnull1 Hfirst2]].
      + pose proof (firstpos_In_positions r1 p (mem_true_In _ _ Hfirst1))
          as Hpin1.
        pose proof
          (label_of_cat_left_reflect r1 r2 p a Hnodup Hpin1 Hlbl)
          as Hlbl1.
        destruct
          (run_from_marked_cat_left_split r1 r2 p rest Hnodup Hpin1 Hrun)
          as [[Hrun1 Hlast_pos1] |
              [prefix [q [b [suffix
                [Heq [Hrun_prefix [Hlast1 [Hfirst2 [Hlbl2 Hrun2]]]]]]]]]].
        * destruct
            (mem_lastpos_cat_left_reflect
               r1 r2 (last_position_from p rest)
               Hnodup Hlast_pos1 Hlast_cat)
            as [Hnull2 Hlast1].
          replace ((p, a) :: rest)
            with (((p, a) :: rest) ++ ([] : list (nat * A)))
            by now rewrite app_nil_r.
          apply MM_Cat.
          -- apply IH1. simpl. repeat split; auto.
             now apply last_position_from_rev_mem.
          -- apply IH2. simpl. exact Hnull2.
        * pose proof (firstpos_In_positions r2 q (mem_true_In _ _ Hfirst2))
            as Hqin2.
          pose proof
            (run_from_marked_last_position_in_positions
               r2 q suffix Hqin2 Hrun2)
            as Hlast_pos2.
          assert (Hlast_cat2 :
            mem (last_position_from q suffix) (lastpos (PCat r1 r2)) = true).
          {
            rewrite Heq in Hlast_cat.
            now rewrite last_position_from_app_nonempty in Hlast_cat.
          }
          pose proof
            (mem_lastpos_cat_right_reflect
               r1 r2 (last_position_from q suffix)
               Hnodup Hlast_pos2 Hlast_cat2)
            as Hlast2.
          rewrite Heq.
          change (matches_marked (PCat r1 r2)
            (((p, a) :: prefix) ++ ((q, b) :: suffix))).
          apply MM_Cat.
          -- apply IH1. simpl. repeat split; auto.
             now apply last_position_from_rev_mem.
          -- apply IH2. simpl. repeat split; auto.
             now apply last_position_from_rev_mem.
      + pose proof (firstpos_In_positions r2 p (mem_true_In _ _ Hfirst2))
          as Hpin2.
        pose proof
          (label_of_cat_right_reflect r1 r2 p a Hnodup Hpin2 Hlbl)
          as Hlbl2.
        pose proof
          (run_from_marked_cat_right_reflect r1 r2 p rest Hnodup Hpin2 Hrun)
          as Hrun2.
        pose proof
          (run_from_marked_last_position_in_positions r2 p rest Hpin2 Hrun2)
          as Hlast_pos2.
        pose proof
          (mem_lastpos_cat_right_reflect
             r1 r2 (last_position_from p rest) Hnodup Hlast_pos2 Hlast_cat)
          as Hlast2.
        change (matches_marked (PCat r1 r2)
          (([] : list (nat * A)) ++ ((p, a) :: rest))).
        apply MM_Cat.
        * apply IH1. simpl. exact Hnull1.
        * apply IH2. simpl. repeat split; auto.
          now apply last_position_from_rev_mem.
  Qed.

  Lemma accepts_marked_star_matches_marked :
    forall (r : positioned_regex A) mw,
      NoDup (positions (PStar r)) ->
      (forall mw, accepts_marked r mw -> matches_marked r mw) ->
      accepts_marked (PStar r) mw ->
      matches_marked (PStar r) mw.
  Proof.
    intros r mw Hnodup Hr_sound Hacc.
    remember (length mw) as n eqn:Hlen.
    revert mw Hlen Hacc.
    induction n as [n IHn] using lt_wf_ind; intros mw Hlen Hacc.
    destruct mw as [| [p a] rest].
    - constructor.
    - simpl in Hacc.
      destruct Hacc as [Hfirst [Hlbl [Hrun Hlast_rev]]].
      pose proof
        (rev_last_position_from_mem
           rest p a (lastpos (PStar r)) Hlast_rev)
        as Hlast_star.
      simpl in Hlast_star.
      simpl in Hlbl.
      pose proof (firstpos_In_positions r p (mem_true_In _ _ Hfirst))
        as Hpin.
      destruct (run_from_marked_star_split r p rest Hpin Hrun)
        as [[Hrun_r _Hlast_pos] |
            [prefix [q [b [suffix
              [Heq [Hrun_prefix [Hlast1 [Hfirst2 [Hlbl2 Hrun2]]]]]]]]]].
      + replace ((p, a) :: rest)
          with (((p, a) :: rest) ++ ([] : list (nat * A)))
          by now rewrite app_nil_r.
        apply MM_StarApp.
        * apply Hr_sound. simpl.
          split; [exact Hfirst |].
          split; [exact Hlbl |].
          split; [exact Hrun_r |].
          now apply last_position_from_rev_mem.
        * discriminate.
        * constructor.
      + assert (Hlast_tail :
          mem (last_position_from q suffix) (lastpos r) = true).
        {
          rewrite Heq in Hlast_star.
          now rewrite last_position_from_app_nonempty in Hlast_star.
        }
        assert (Hacc_tail : accepts_marked (PStar r) ((q, b) :: suffix)).
        {
          simpl.
          split; [exact Hfirst2 |].
          split; [simpl; exact Hlbl2 |].
          split; [exact Hrun2 |].
          now apply last_position_from_rev_mem.
        }
        assert (Hlen_tail : length ((q, b) :: suffix) < n).
        {
          rewrite Hlen.
          rewrite Heq.
          simpl.
          rewrite length_app.
          simpl. lia.
        }
        pose proof
          (IHn (length ((q, b) :: suffix))
             Hlen_tail ((q, b) :: suffix) eq_refl Hacc_tail)
          as Hmatch_tail.
        rewrite Heq.
        change (matches_marked (PStar r)
          (((p, a) :: prefix) ++ ((q, b) :: suffix))).
        apply MM_StarApp.
        * apply Hr_sound. simpl.
          split; [exact Hfirst |].
          split; [exact Hlbl |].
          split; [exact Hrun_prefix |].
          now apply last_position_from_rev_mem.
        * discriminate.
        * exact Hmatch_tail.
  Qed.

  Lemma accepts_marked_alt_matches_marked :
    forall (r1 r2 : positioned_regex A) mw,
      NoDup (positions (PAlt r1 r2)) ->
      (forall mw, accepts_marked r1 mw -> matches_marked r1 mw) ->
      (forall mw, accepts_marked r2 mw -> matches_marked r2 mw) ->
      accepts_marked (PAlt r1 r2) mw ->
      matches_marked (PAlt r1 r2) mw.
  Proof.
    intros r1 r2 mw Hnodup IH1 IH2 Hacc.
    destruct mw as [| [p a] rest].
    - now apply accepts_marked_empty_matches_marked.
    - simpl in Hacc.
      destruct Hacc as [Hfirst [Hlbl [Hrun Hlast]]].
      apply mem_union_elim in Hfirst as [Hfirst | Hfirst].
      + pose proof (firstpos_In_positions r1 p (mem_true_In _ _ Hfirst)) as Hpin.
        pose proof
          (label_of_alt_left_reflect r1 r2 p a Hnodup Hpin Hlbl)
          as Hlbl1.
        pose proof
          (run_from_marked_alt_left_reflect r1 r2 p rest Hnodup Hpin Hrun)
          as Hrun1.
        pose proof
          (run_from_marked_last_position_in_positions r1 p rest Hpin Hrun1)
          as Hlast_pos.
        pose proof
          (mem_lastpos_alt_left_reflect
             r1 r2 (last_position_from p rest) Hnodup Hlast_pos)
          as Hlast_reflect.
        apply MM_AltL.
        apply IH1.
        simpl. repeat split; auto.
        apply last_position_from_rev_mem.
        apply Hlast_reflect.
        eapply rev_last_position_from_mem. exact Hlast.
      + pose proof (firstpos_In_positions r2 p (mem_true_In _ _ Hfirst)) as Hpin.
        pose proof
          (label_of_alt_right_reflect r1 r2 p a Hnodup Hpin Hlbl)
          as Hlbl2.
        pose proof
          (run_from_marked_alt_right_reflect r1 r2 p rest Hnodup Hpin Hrun)
          as Hrun2.
        pose proof
          (run_from_marked_last_position_in_positions r2 p rest Hpin Hrun2)
          as Hlast_pos.
        pose proof
          (mem_lastpos_alt_right_reflect
             r1 r2 (last_position_from p rest) Hnodup Hlast_pos)
          as Hlast_reflect.
        apply MM_AltR.
        apply IH2.
        simpl. repeat split; auto.
        apply last_position_from_rev_mem.
        apply Hlast_reflect.
        eapply rev_last_position_from_mem. exact Hlast.
  Qed.

  Theorem accepts_marked_matches_marked :
    forall (pr : positioned_regex A) mw,
      NoDup (positions pr) ->
      accepts_marked pr mw ->
      matches_marked pr mw.
  Proof.
    induction pr; intros mw Hnodup Hacc.
    - destruct mw as [| [p a] rest].
      + simpl in Hacc. discriminate.
      + simpl in Hacc. destruct Hacc as [Hfirst _]. discriminate.
    - destruct mw as [| [p a] rest].
      + constructor.
      + simpl in Hacc. destruct Hacc as [Hfirst _]. discriminate.
    - now apply accepts_marked_atom_matches_marked.
    - eapply accepts_marked_alt_matches_marked; eauto.
      + intros mw' H. eapply IHpr1; eauto.
        now apply NoDup_app_left in Hnodup.
      + intros mw' H. eapply IHpr2; eauto.
        now apply NoDup_app_right in Hnodup.
    - eapply accepts_marked_cat_matches_marked; eauto.
      + intros mw' H. eapply IHpr1; eauto.
        now apply NoDup_app_left in Hnodup.
      + intros mw' H. eapply IHpr2; eauto.
        now apply NoDup_app_right in Hnodup.
    - eapply accepts_marked_star_matches_marked; eauto.
  Qed.

  Corollary accepts_marked_label_matches_marked :
    forall (r : regex A) mw,
      accepts_marked (label r) mw ->
      matches_marked (label r) mw.
  Proof.
    intros r mw Hacc.
    eapply accepts_marked_matches_marked; eauto.
    apply label_positions_nodup.
  Qed.

  Theorem position_nfa_accepting_path_accepts_marked :
    forall
      (label_matches : A -> A -> bool)
      (r : positioned_regex A)
      w,
      (forall x y, label_matches x y = true -> x = y) ->
      accepting_path (position_nfa label_matches r) w ->
      exists mw,
        symbols mw = w /\
        accepts_marked r mw.
  Proof.
    intros label_matches r w Hsound Hacc.
    destruct Hacc as [q0 [qf [Hstart [Hpath Hfinal]]]].
    simpl in Hstart.
    destruct Hstart as [Hq0 | []]. subst q0.
    destruct w as [| a w].
    - inversion Hpath; subst.
      exists []. simpl. split; auto.
    - inversion Hpath as [| st a' st' w' qf' Hstep Htail]; subst.
      unfold position_nfa in Hstep. simpl in Hstep.
      destruct (matching_positions_in_state _ _ _ _ _ Hstep)
        as [p [b [Hst' [Hfirst [Hlbl Hmatch]]]]].
      subst st'.
      apply Hsound in Hmatch. subst b.
      destruct
        (position_nfa_path_from_position_accepts_tail
           label_matches r p w qf Hsound Htail Hfinal)
        as [mw [Hsym [Hrun Hlast]]].
      exists ((p, a) :: mw). simpl.
      split; [now rewrite Hsym |].
      repeat split; auto.
      now apply last_position_from_rev_mem.
  Qed.

  Theorem position_nfa_accepting_path_matches_marked :
    forall
      (label_matches : A -> A -> bool)
      (r : positioned_regex A)
      w,
      NoDup (positions r) ->
      (forall x y, label_matches x y = true -> x = y) ->
      accepting_path (position_nfa label_matches r) w ->
      exists mw,
        symbols mw = w /\
        matches_marked r mw.
  Proof.
    intros label_matches r w Hnodup Hsound Hpath.
    destruct
      (position_nfa_accepting_path_accepts_marked
         label_matches r w Hsound Hpath)
      as [mw [Hsym Hacc]].
    exists mw. split; auto.
    eapply accepts_marked_matches_marked; eauto.
  Qed.

  Corollary position_nfa_accepting_path_label_matches_marked :
    forall
      (label_matches : A -> A -> bool)
      (r : regex A)
      w,
      (forall x y, label_matches x y = true -> x = y) ->
      accepting_path (position_nfa label_matches (label r)) w ->
      exists mw,
        symbols mw = w /\
        matches_marked (label r) mw.
  Proof.
    intros label_matches r w Hsound Hpath.
    eapply position_nfa_accepting_path_matches_marked; eauto.
    apply label_positions_nodup.
  Qed.

  Theorem matches_marked_accepts_marked :
    forall (pr : positioned_regex A) mw,
      NoDup (positions pr) ->
      matches_marked pr mw ->
      accepts_marked pr mw.
  Proof.
    intros pr mw Hnodup Hm.
    destruct mw as [| [p a] rest].
    - simpl. now apply matches_marked_nullable.
    - pose proof
        (matches_marked_accepts_marked_boundary
           pr ((p, a) :: rest) Hnodup Hm)
        as [Hfirst [Hlbl Hlast]].
      simpl.
      repeat split.
      + exact Hfirst.
      + exact Hlbl.
      + eapply matches_marked_run_from_marked; eauto.
      + now apply last_position_from_rev_mem.
  Qed.

  Corollary matches_marked_label_accepts_marked :
    forall (r : regex A) mw,
      matches_marked (label r) mw ->
      accepts_marked (label r) mw.
  Proof.
    intros r mw Hm.
    eapply matches_marked_accepts_marked; eauto.
    apply label_positions_nodup.
  Qed.

  Theorem matches_marked_accepts_marked_iff :
    forall (pr : positioned_regex A) mw,
      NoDup (positions pr) ->
      (matches_marked pr mw <-> accepts_marked pr mw).
  Proof.
    intros pr mw Hnodup. split.
    - now apply matches_marked_accepts_marked.
    - now apply accepts_marked_matches_marked.
  Qed.

  Corollary matches_marked_label_accepts_marked_iff :
    forall (r : regex A) mw,
      matches_marked (label r) mw <-> accepts_marked (label r) mw.
  Proof.
    intros r mw.
    apply matches_marked_accepts_marked_iff.
    apply label_positions_nodup.
  Qed.

  Lemma run_from_marked_position_path :
    forall
      (label_matches : A -> A -> bool)
      (r : positioned_regex A)
      p mw,
      (forall x, label_matches x x = true) ->
      run_from_marked (followpos r) (label_of r) p mw ->
      path_from
        (position_nfa label_matches r)
        (Some p)
        (symbols mw)
        (Some (last_position_from p mw)).
  Proof.
    intros label_matches r p mw Hrefl.
    revert p.
    induction mw as [| [q a] mw IH]; intros p Hrun; simpl in *.
    - constructor.
    - destruct Hrun as [Hfollow [Hlbl Hrun]].
      eapply Path_cons.
      + unfold position_nfa. simpl.
        eapply mem_matching_positions; eauto.
      + apply IH; exact Hrun.
  Qed.

  Theorem accepts_marked_position_nfa_accepting_path :
    forall
      (label_matches : A -> A -> bool)
      (r : positioned_regex A)
      mw,
      (forall x, label_matches x x = true) ->
      accepts_marked r mw ->
      accepting_path (position_nfa label_matches r) (symbols mw).
  Proof.
    intros label_matches r mw Hrefl Hacc.
    destruct mw as [| [p a] mw].
    - simpl in Hacc.
      exists None, None.
      repeat split; simpl; auto.
      constructor.
    - simpl in Hacc.
      destruct Hacc as [Hfirst [Hlbl [Hrun Hlast]]].
      exists None, (Some (last_position_from p mw)).
      repeat split.
      + simpl. auto.
      + simpl.
        eapply Path_cons.
        * unfold position_nfa. simpl.
          eapply mem_matching_positions; eauto.
        * apply run_from_marked_position_path; auto.
      + unfold position_nfa. simpl.
        eapply rev_last_position_from_mem. exact Hlast.
  Qed.

  Theorem regex_match_position_nfa_accepting_path :
    forall
      (label_matches : A -> A -> bool)
      (r : regex A)
      w,
      (forall x, label_matches x x = true) ->
      matches r w ->
      exists mw,
        symbols mw = w /\
        accepting_path (position_nfa label_matches (label r)) w.
  Proof.
    intros label_matches r w Hrefl Hm.
    destruct (label_semantics_preserved r w Hm) as [mw [Hsym Hmm]].
    exists mw. split; auto.
    rewrite <- Hsym.
    apply accepts_marked_position_nfa_accepting_path; auto.
    now apply matches_marked_label_accepts_marked.
  Qed.

End PositionCorrectness.
