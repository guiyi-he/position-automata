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

  Definition reachb
      (vertices : list V)
      (edge : graph_edge)
      (fuel : nat)
      (x y : V) : bool :=
    dfs vertices edge (S fuel) [] [x] y.

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

  Lemma reachb_sound :
    forall vertices edge fuel x y,
      reachb vertices edge fuel x y = true ->
      walk edge x y.
  Proof.
    intros vertices edge fuel x y H.
    unfold reachb in H.
    eapply dfs_sound_from; eauto.
    intros z Hz.
    simpl in Hz.
    destruct Hz as [Hz | []].
    subst. constructor.
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
End GraphAlgorithms.
