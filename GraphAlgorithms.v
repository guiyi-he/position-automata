From Stdlib Require Import List Bool Arith Lia.
Import ListNotations.

(** Small executable graph routines over an explicit finite vertex list.

    The algorithms are intentionally simple.  They are meant as verified
    building blocks for finite automata graph criteria, not as asymptotically
    optimal implementations. *)

Section GraphAlgorithms.
  Context {V : Type}.
  Context (eqb : V -> V -> bool).
  Context (eqb_sound : forall x y, eqb x y = true -> x = y).

  Definition graph_edge := V -> V -> bool.

  Inductive walk (edge : graph_edge) : V -> V -> Prop :=
  | Walk_refl :
      forall x, walk edge x x
  | Walk_step :
      forall x y z,
        edge x y = true ->
        walk edge y z ->
        walk edge x z.

  Lemma walk_trans :
    forall edge x y z,
      walk edge x y ->
      walk edge y z ->
      walk edge x z.
  Proof.
    intros edge x y z Hxy Hyz.
    induction Hxy as [x| x y' z' Hedge _ IH]; auto.
    eapply Walk_step; eauto.
  Qed.

  Fixpoint path_of_lengthb
      (vertices : list V)
      (edge : graph_edge)
      (n : nat)
      (x y : V) : bool :=
    match n with
    | O => eqb x y
    | S n' =>
        existsb
          (fun z => edge x z && path_of_lengthb vertices edge n' z y)
          vertices
    end.

  Fixpoint inb (x : V) (xs : list V) : bool :=
    match xs with
    | [] => false
    | y :: ys => eqb x y || inb x ys
    end.

  Definition pair_inb (x y : V) (rel : list (V * V)) : bool :=
    existsb
      (fun xy => eqb x (fst xy) && eqb y (snd xy))
      rel.

  Definition add_pair (x y : V) (rel : list (V * V))
      : list (V * V) :=
    if pair_inb x y rel then rel else (x, y) :: rel.

  Definition all_pairs (vertices : list V) : list (V * V) :=
    list_prod vertices vertices.

  Definition seed_reach (vertices : list V) (edge : graph_edge)
      : list (V * V) :=
    fold_right
      (fun xy rel =>
         let x := fst xy in
         let y := snd xy in
         if eqb x y || edge x y then add_pair x y rel else rel)
      []
      (all_pairs vertices).

  Definition close_at
      (vertices : list V)
      (k : V)
      (rel : list (V * V)) : list (V * V) :=
    fold_right
      (fun xy acc =>
         let x := fst xy in
         let y := snd xy in
         if pair_inb x k rel && pair_inb k y rel
         then add_pair x y acc
         else acc)
      rel
      (all_pairs vertices).

  Fixpoint reach_pairs
      (vertices pivots : list V)
      (edge : graph_edge) : list (V * V) :=
    match pivots with
    | [] => seed_reach vertices edge
    | k :: pivots' =>
        close_at vertices k (reach_pairs vertices pivots' edge)
    end.

  Definition reachability_relation
      (vertices : list V)
      (edge : graph_edge)
      (fuel : nat) : list (V * V) :=
    reach_pairs vertices (firstn fuel vertices) edge.

  Definition successors
      (vertices : list V)
      (edge : graph_edge)
      (x : V) : list V :=
    filter (edge x) vertices.

  Fixpoint add_fresh
      (xs seen todo : list V) : list V :=
    match xs with
    | [] => todo
    | x :: xs' =>
        let already_seen := inb x seen || inb x todo in
        add_fresh xs' seen (if already_seen then todo else x :: todo)
    end.

  Fixpoint dfs
      (vertices : list V)
      (edge : graph_edge)
      (fuel : nat)
      (seen todo : list V)
      (target : V) : bool :=
    match fuel with
    | O => false
    | S fuel' =>
        match todo with
        | [] => false
        | x :: todo' =>
            if inb x seen then dfs vertices edge fuel' seen todo' target
            else if eqb x target then true
            else
              dfs
                vertices
                edge
                fuel'
                (x :: seen)
                (add_fresh (successors vertices edge x) (x :: seen) todo')
                target
        end
    end.

  Fixpoint closeb (edge : graph_edge) (vertices : list V)
      : graph_edge :=
    match vertices with
    | [] => fun x y => eqb x y || edge x y
    | k :: vertices' =>
        let reach' := closeb edge vertices' in
        fun x y => reach' x y || (reach' x k && reach' k y)
    end.

  Definition reachb
      (vertices : list V)
      (edge : graph_edge)
      (fuel : nat)
      (x y : V) : bool :=
    pair_inb x y (reachability_relation vertices edge fuel).

  Definition connectedb
      (vertices : list V)
      (edge : graph_edge)
      (fuel : nat)
      (x y : V) : bool :=
    reachb vertices edge fuel x y && reachb vertices edge fuel y x.

  Fixpoint max_nats (xs : list nat) : nat :=
    match xs with
    | [] => 0
    | x :: xs' => Nat.max x (max_nats xs')
    end.

  Fixpoint max_special_path_from
      (vertices : list V)
      (edge special : graph_edge)
      (fuel : nat)
      (x : V) : nat :=
    match fuel with
    | O => 0
    | S fuel' =>
        max_nats
          (map
             (fun y =>
                if edge x y
                then
                  (if special x y then 1 else 0)
                  + max_special_path_from vertices edge special fuel' y
                else 0)
             vertices)
    end.

  Definition max_special_edges
      (vertices : list V)
      (edge special : graph_edge)
      (fuel : nat) : nat :=
    max_nats
      (map (max_special_path_from vertices edge special fuel) vertices).

  Lemma path_of_lengthb_sound :
    forall vertices edge n x y,
      path_of_lengthb vertices edge n x y = true ->
      walk edge x y.
  Proof.
    intros vertices edge n.
    induction n as [| n IH]; intros x y H.
    - simpl in H.
      apply eqb_sound in H. subst. constructor.
    - simpl in H.
      apply existsb_exists in H as [z [_ Hz]].
      apply andb_true_iff in Hz as [Hedge Hpath].
      eapply Walk_step.
      + exact Hedge.
      + now apply IH.
  Qed.

  Lemma successors_sound :
    forall vertices edge x y,
      In y (successors vertices edge x) ->
      edge x y = true.
  Proof.
    intros vertices edge x y H.
    unfold successors in H.
    apply filter_In in H as [_ Hedge].
    exact Hedge.
  Qed.

  Lemma add_fresh_In :
    forall xs seen todo y,
      In y (add_fresh xs seen todo) ->
      In y todo \/ In y xs.
  Proof.
    induction xs as [| x xs IH]; intros seen todo y H; simpl in H.
    - left. exact H.
    - apply IH in H as [Htodo | Hxs].
      + destruct (inb x seen || inb x todo) eqn:Halready.
        * left. exact Htodo.
        * simpl in Htodo.
          destruct Htodo as [Hy | Hy].
          -- subst. right. left. reflexivity.
          -- left. exact Hy.
      + right. right. exact Hxs.
  Qed.

  Lemma dfs_sound_from :
    forall vertices edge fuel seen todo target source,
      (forall z, In z todo -> walk edge source z) ->
      dfs vertices edge fuel seen todo target = true ->
      walk edge source target.
  Proof.
    intros vertices edge fuel.
    induction fuel as [| fuel IH]; intros seen todo target source Htodo Hdfs.
    - discriminate.
    - destruct todo as [| x todo']; simpl in Hdfs; try discriminate.
      destruct (inb x seen) eqn:Hseen.
      + apply IH with (seen := seen) (todo := todo').
        * intros z Hz. apply Htodo. simpl. auto.
        * exact Hdfs.
      + destruct (eqb x target) eqn:Htarget.
        * apply eqb_sound in Htarget. subst.
          apply Htodo. simpl. auto.
        * apply IH with
            (seen := x :: seen)
            (todo := add_fresh (successors vertices edge x) (x :: seen) todo').
          -- intros z Hz.
             apply add_fresh_In in Hz as [Hz | Hz].
             ++ apply Htodo. simpl. auto.
             ++ eapply walk_trans.
                ** apply Htodo. simpl. auto.
                ** eapply Walk_step.
                   --- apply successors_sound in Hz. exact Hz.
                   --- constructor.
          -- exact Hdfs.
  Qed.

  Lemma closeb_sound :
    forall vertices edge x y,
      closeb edge vertices x y = true ->
      walk edge x y.
  Proof.
    induction vertices as [| k vertices IH]; simpl; intros edge x y H.
    - apply Bool.orb_true_iff in H as [Heq | Hedge].
      + apply eqb_sound in Heq. subst. constructor.
      + eapply Walk_step; eauto. constructor.
    - apply Bool.orb_true_iff in H as [Hxy | Hvia].
      + now apply IH.
      + apply andb_true_iff in Hvia as [Hxk Hky].
        eapply walk_trans.
        * exact (IH edge x k Hxk).
        * exact (IH edge k y Hky).
  Qed.

  Lemma pair_inb_sound :
    forall rel x y,
      pair_inb x y rel = true ->
      exists p q,
        In (p, q) rel /\ x = p /\ y = q.
  Proof.
    unfold pair_inb.
    intros rel x y H.
    apply existsb_exists in H as [[p q] [Hin Heq]].
    simpl in Heq.
    apply andb_true_iff in Heq as [Hx Hy].
    apply eqb_sound in Hx.
    apply eqb_sound in Hy.
    subst.
    exists p, q.
    repeat split; assumption.
  Qed.

  Lemma pair_inb_complete :
    (forall x y, x = y -> eqb x y = true) ->
    forall rel x y,
      In (x, y) rel ->
      pair_inb x y rel = true.
  Proof.
    intros eqb_complete rel x y Hin.
    unfold pair_inb.
    apply existsb_exists.
    exists (x, y).
    split; auto.
    simpl.
    apply andb_true_iff.
    split; apply eqb_complete; reflexivity.
  Qed.

  Lemma pair_inb_add_preserve :
    forall rel x y p q,
      pair_inb x y rel = true ->
      pair_inb x y (add_pair p q rel) = true.
  Proof.
    intros rel x y p q H.
    unfold add_pair.
    destruct (pair_inb p q rel) eqn:Hpresent; auto.
    simpl.
    rewrite H.
    apply Bool.orb_true_r.
  Qed.

  Lemma pair_inb_add_hit :
    (forall x y, x = y -> eqb x y = true) ->
    forall rel x y,
      pair_inb x y (add_pair x y rel) = true.
  Proof.
    intros eqb_complete rel x y.
    unfold add_pair.
    destruct (pair_inb x y rel) eqn:Hpresent; auto.
    simpl.
    rewrite (eqb_complete x x eq_refl).
    rewrite (eqb_complete y y eq_refl).
    reflexivity.
  Qed.

  Lemma add_pair_sound :
    forall edge rel p q,
      (forall x y, pair_inb x y rel = true -> walk edge x y) ->
      walk edge p q ->
      forall x y,
        pair_inb x y (add_pair p q rel) = true ->
        walk edge x y.
  Proof.
    intros edge rel p q Hrel Hpq x y H.
    unfold add_pair in H.
    destruct (pair_inb p q rel) eqn:Hpresent.
    - now apply Hrel.
    - simpl in H.
      apply Bool.orb_true_iff in H as [Hhead | Htail].
      + apply andb_true_iff in Hhead as [Hx Hy].
        apply eqb_sound in Hx.
        apply eqb_sound in Hy.
        subst. exact Hpq.
      + now apply Hrel.
  Qed.

  Lemma seed_reach_sound :
    forall vertices edge x y,
      pair_inb x y (seed_reach vertices edge) = true ->
      walk edge x y.
  Proof.
    intros vertices edge.
    unfold seed_reach.
    remember (all_pairs vertices) as pairs.
    clear Heqpairs vertices.
    induction pairs as [| [p q] pairs IH]; simpl; intros x y H.
    - discriminate.
    - destruct (eqb p q || edge p q) eqn:Hedge.
      + refine (add_pair_sound edge _ p q IH _ x y H).
        apply Bool.orb_true_iff in Hedge as [Heq | Hstep].
        * pose proof (eqb_sound p q Heq) as Hpq.
          subst q. exact (Walk_refl edge p).
        * exact (Walk_step edge p q q Hstep (Walk_refl edge q)).
      + now apply IH.
  Qed.

  Lemma close_at_sound :
    forall vertices edge k rel,
      (forall x y, pair_inb x y rel = true -> walk edge x y) ->
      forall x y,
        pair_inb x y (close_at vertices k rel) = true ->
        walk edge x y.
  Proof.
    intros vertices edge k rel Hrel.
    unfold close_at.
    remember (all_pairs vertices) as pairs.
    clear Heqpairs vertices.
    induction pairs as [| [p q] pairs IH]; simpl; intros x y H.
    - now apply Hrel.
    - destruct (pair_inb p k rel && pair_inb k q rel) eqn:Hvia.
      + refine (add_pair_sound edge _ p q IH _ x y H).
        apply andb_true_iff in Hvia as [Hpk Hkq].
        exact (walk_trans edge p k q (Hrel p k Hpk) (Hrel k q Hkq)).
      + now apply IH.
  Qed.

  Lemma reach_pairs_sound :
    forall vertices pivots edge x y,
      pair_inb x y (reach_pairs vertices pivots edge) = true ->
      walk edge x y.
  Proof.
    intros vertices pivots.
    induction pivots as [| k pivots IH]; intros edge x y H; simpl in H.
    - now apply seed_reach_sound in H.
    - eapply close_at_sound; eauto.
  Qed.

  Lemma reachb_sound :
    forall vertices edge fuel x y,
      reachb vertices edge fuel x y = true ->
      walk edge x y.
  Proof.
    intros vertices edge fuel x y H.
    unfold reachb, reachability_relation in H.
    now apply reach_pairs_sound in H.
  Qed.

  Lemma connectedb_sound :
    forall vertices edge fuel x y,
      connectedb vertices edge fuel x y = true ->
      walk edge x y /\ walk edge y x.
  Proof.
    intros vertices edge fuel x y H.
    unfold connectedb in H.
    apply andb_true_iff in H as [Hxy Hyx].
    split.
    - eapply reachb_sound; eauto.
    - eapply reachb_sound; eauto.
  Qed.

  Lemma closeb_refl :
    (forall x y, x = y -> eqb x y = true) ->
    forall vertices edge x,
      closeb edge vertices x x = true.
  Proof.
    intros eqb_complete vertices.
    induction vertices as [| k vertices IH]; simpl; intros edge x.
    - apply Bool.orb_true_iff. left.
      apply eqb_complete. reflexivity.
    - apply Bool.orb_true_iff. left.
      apply IH.
  Qed.

  Lemma closeb_edge :
    forall vertices edge x y,
      edge x y = true ->
      closeb edge vertices x y = true.
  Proof.
    induction vertices as [| k vertices IH]; simpl; intros edge x y Hedge.
    - apply Bool.orb_true_iff. right. exact Hedge.
    - apply Bool.orb_true_iff. left.
      now apply IH.
  Qed.

  Lemma closeb_trans :
    forall vertices edge pivot x y,
      In pivot vertices ->
      closeb edge vertices x pivot = true ->
      closeb edge vertices pivot y = true ->
      closeb edge vertices x y = true.
  Proof.
    induction vertices as [| k vertices IH]; simpl; intros edge pivot x y Hin Hxp Hpy.
    - contradiction.
    - destruct Hin as [Hpivot | Hin].
      + subst pivot.
        apply Bool.orb_true_iff.
        right.
        apply andb_true_iff.
        split.
        * apply Bool.orb_true_iff in Hxp as [Hxp | Hxp].
          -- exact Hxp.
          -- apply andb_true_iff in Hxp as [Hxp _]. exact Hxp.
        * apply Bool.orb_true_iff in Hpy as [Hpy | Hpy].
          -- exact Hpy.
          -- apply andb_true_iff in Hpy as [_ Hpy]. exact Hpy.
      + apply Bool.orb_true_iff in Hxp as [Hxp | Hxp];
          apply Bool.orb_true_iff in Hpy as [Hpy | Hpy].
        * apply Bool.orb_true_iff. left.
          eapply IH; eauto.
        * apply andb_true_iff in Hpy as [Hpk Hky].
          apply Bool.orb_true_iff. right.
          apply andb_true_iff. split; auto.
          eapply IH; eauto.
        * apply andb_true_iff in Hxp as [Hxk Hkp].
          apply Bool.orb_true_iff. right.
          apply andb_true_iff. split; auto.
          eapply IH; eauto.
        * apply andb_true_iff in Hxp as [Hxk _].
          apply andb_true_iff in Hpy as [_ Hky].
          apply Bool.orb_true_iff. right.
          now apply andb_true_iff.
  Qed.

  Lemma all_pairs_complete :
    forall vertices x y,
      In x vertices ->
      In y vertices ->
      In (x, y) (all_pairs vertices).
  Proof.
    intros vertices x y Hx Hy.
    unfold all_pairs.
    now apply in_prod.
  Qed.

  Lemma seed_reach_complete :
    (forall x y, x = y -> eqb x y = true) ->
    forall vertices edge x y,
      In x vertices ->
      In y vertices ->
      (eqb x y || edge x y) = true ->
      pair_inb x y (seed_reach vertices edge) = true.
  Proof.
    intros eqb_complete vertices edge x y Hx Hy Hedge.
    unfold seed_reach.
    assert (Hinpair : In (x, y) (all_pairs vertices)).
    { now apply all_pairs_complete. }
    remember (all_pairs vertices) as pairs.
    clear Heqpairs Hx Hy vertices.
    revert x y Hinpair Hedge.
    induction pairs as [| [p q] pairs IH]; simpl; intros x y Hinpair Hedge.
    - contradiction.
    - destruct Hinpair as [Hhead | Htail].
      + inversion Hhead; subst p q.
        rewrite Hedge.
        now apply pair_inb_add_hit.
      + destruct (eqb p q || edge p q).
        * apply pair_inb_add_preserve.
          now apply IH.
        * now apply IH.
  Qed.

  Lemma close_at_preserve :
    forall vertices k rel x y,
      pair_inb x y rel = true ->
      pair_inb x y (close_at vertices k rel) = true.
  Proof.
    intros vertices k rel x y H.
    unfold close_at.
    remember (all_pairs vertices) as pairs.
    clear Heqpairs vertices.
    induction pairs as [| [p q] pairs IH]; simpl.
    - exact H.
    - destruct (pair_inb p k rel && pair_inb k q rel).
      + apply pair_inb_add_preserve. exact IH.
      + exact IH.
  Qed.

  Lemma close_at_complete :
    (forall x y, x = y -> eqb x y = true) ->
    forall vertices k rel x y,
      In x vertices ->
      In y vertices ->
      pair_inb x k rel = true ->
      pair_inb k y rel = true ->
      pair_inb x y (close_at vertices k rel) = true.
  Proof.
    intros eqb_complete vertices k rel x y Hx Hy Hxk Hky.
    unfold close_at.
    assert (Hinpair : In (x, y) (all_pairs vertices)).
    { now apply all_pairs_complete. }
    remember (all_pairs vertices) as pairs.
    clear Heqpairs Hx Hy vertices.
    revert x y Hinpair Hxk Hky.
    induction pairs as [| [p q] pairs IH]; simpl; intros x y Hinpair Hxk Hky.
    - contradiction.
    - destruct Hinpair as [Hhead | Htail].
      + inversion Hhead; subst p q.
        rewrite Hxk, Hky.
        simpl.
        now apply pair_inb_add_hit.
      + destruct (pair_inb p k rel && pair_inb k q rel).
        * apply pair_inb_add_preserve.
          now apply IH.
        * now apply IH.
  Qed.

  Lemma reach_pairs_complete_closeb :
    (forall x y, x = y -> eqb x y = true) ->
    forall vertices pivots edge x y,
      (forall k, In k pivots -> In k vertices) ->
      In x vertices ->
      In y vertices ->
      closeb edge pivots x y = true ->
      pair_inb x y (reach_pairs vertices pivots edge) = true.
  Proof.
    intros eqb_complete vertices pivots.
    induction pivots as [| k pivots IH]; intros edge x y Hpivots Hx Hy Hclose;
      simpl in Hclose; simpl.
    - now apply seed_reach_complete.
    - apply Bool.orb_true_iff in Hclose as [Htail | Hvia].
      + apply close_at_preserve.
        eapply IH; eauto.
        intros z Hz. apply Hpivots. now right.
      + apply andb_true_iff in Hvia as [Hxk Hky].
        apply close_at_complete; auto.
        * eapply IH; eauto.
          -- intros z Hz. apply Hpivots. now right.
          -- apply Hpivots. now left.
        * eapply IH; eauto.
          -- intros z Hz. apply Hpivots. now right.
          -- apply Hpivots. now left.
  Qed.

  Lemma walk_end_in :
    forall vertices edge x y,
      In x vertices ->
      (forall p q, In p vertices -> edge p q = true -> In q vertices) ->
      walk edge x y ->
      In y vertices.
  Proof.
    intros vertices edge x y Hx Hclosed Hwalk.
    induction Hwalk as [x| x z y Hedge _ IH].
    - exact Hx.
    - apply IH.
      eapply Hclosed; eauto.
  Qed.

  Lemma closeb_walk_complete :
    (forall x y, x = y -> eqb x y = true) ->
    forall vertices edge x y,
      In x vertices ->
      (forall p q, In p vertices -> edge p q = true -> In q vertices) ->
      walk edge x y ->
      closeb edge vertices x y = true.
  Proof.
    intros eqb_complete vertices edge x y Hx Hclosed Hwalk.
    induction Hwalk as [x| x z y Hedge _ IH].
    - now apply closeb_refl.
    - assert (Hz : In z vertices) by (eapply Hclosed; eauto).
      eapply closeb_trans with (pivot := z).
      + exact Hz.
      + now apply closeb_edge.
      + apply IH; exact Hz.
  Qed.

  Lemma reachb_complete :
    (forall x y, x = y -> eqb x y = true) ->
    forall vertices edge fuel x y,
      length vertices <= fuel ->
      In x vertices ->
      (forall p q, In p vertices -> edge p q = true -> In q vertices) ->
      walk edge x y ->
      reachb vertices edge fuel x y = true.
  Proof.
    intros eqb_complete vertices edge fuel x y Hfuel Hx Hclosed Hwalk.
    assert (Hy : In y vertices).
    { eapply walk_end_in; eauto. }
    unfold reachb, reachability_relation.
    rewrite firstn_all2 by lia.
    eapply (reach_pairs_complete_closeb eqb_complete vertices vertices edge x y).
    - intros k Hk. exact Hk.
    - exact Hx.
    - exact Hy.
    - eapply closeb_walk_complete; eauto.
  Qed.

  Lemma connectedb_complete :
    (forall x y, x = y -> eqb x y = true) ->
    forall vertices edge fuel x y,
      length vertices <= fuel ->
      In x vertices ->
      In y vertices ->
      (forall p q, In p vertices -> edge p q = true -> In q vertices) ->
      walk edge x y ->
      walk edge y x ->
      connectedb vertices edge fuel x y = true.
  Proof.
    intros eqb_complete vertices edge fuel x y Hfuel Hx Hy Hclosed Hxy Hyx.
    unfold connectedb.
    apply andb_true_iff. split.
    - eapply reachb_complete; eauto.
    - eapply reachb_complete; eauto.
  Qed.
End GraphAlgorithms.
