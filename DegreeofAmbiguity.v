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

Lemma sum_nats_map_In_pos :
  forall {B : Type} (f : B -> nat) x xs,
    In x xs ->
    0 < f x ->
    0 < sum_nats (map f xs).
Proof.
  intros B f x xs Hin Hpos.
  induction xs as [| y xs IH]; simpl in *; try contradiction.
  destruct Hin as [Heq | Hin].
  - subst. lia.
  - specialize (IH Hin). lia.
Qed.

Lemma sum_nats_map_In_ge :
  forall {B : Type} (f : B -> nat) x xs,
    In x xs ->
    f x <= sum_nats (map f xs).
Proof.
  intros B f x xs Hin.
  induction xs as [| y xs IH]; simpl in *; try contradiction.
  destruct Hin as [Heq | Hin].
  - subst. lia.
  - specialize (IH Hin). lia.
Qed.

Lemma sum_nats_map_ge_pointwise :
  forall {B : Type} (f g : B -> nat) xs,
    (forall x, In x xs -> g x <= f x) ->
    sum_nats (map g xs) <= sum_nats (map f xs).
Proof.
  intros B f g xs Hle.
  induction xs as [| x xs IH]; simpl.
  - lia.
  - assert (Hx : g x <= f x) by (apply Hle; simpl; auto).
    assert (Hxs : sum_nats (map g xs) <= sum_nats (map f xs)).
    {
      apply IH. intros y Hy. apply Hle. simpl; auto.
    }
    lia.
Qed.

Lemma sum_nats_map_mul_r :
  forall {B : Type} (f : B -> nat) xs n,
    sum_nats (map (fun x => f x * n) xs) =
      sum_nats (map f xs) * n.
Proof.
  intros B f xs n.
  induction xs as [| x xs IH]; simpl.
  - lia.
  - rewrite IH. nia.
Qed.

Lemma sum_nats_map_add :
  forall {B : Type} (f g : B -> nat) xs,
    sum_nats (map (fun x => f x + g x) xs) =
      sum_nats (map f xs) + sum_nats (map g xs).
Proof.
  intros B f g xs.
  induction xs as [| x xs IH]; simpl.
  - reflexivity.
  - rewrite IH. lia.
Qed.

Lemma sum_nats_map_le_const :
  forall {B : Type} (f : B -> nat) xs c,
    (forall x, In x xs -> f x <= c) ->
    sum_nats (map f xs) <= length xs * c.
Proof.
  intros B f xs c Hle.
  induction xs as [| x xs IH]; simpl.
  - lia.
  - assert (Hx : f x <= c) by (apply Hle; simpl; auto).
    assert (Hxs : sum_nats (map f xs) <= length xs * c).
    {
      apply IH. intros y Hy. apply Hle. simpl; auto.
    }
    lia.
Qed.

Lemma length_concat_map :
  forall {B C : Type} (f : B -> list C) xs,
    length (concat (map f xs)) =
      sum_nats (map (fun x => length (f x)) xs).
Proof.
  intros B C f xs.
  induction xs as [| x xs IH]; simpl.
  - reflexivity.
  - rewrite length_app. rewrite IH. reflexivity.
Qed.

Lemma sum_nats_map_const :
  forall {B : Type} (xs : list B) c,
    sum_nats (map (fun _ => c) xs) = length xs * c.
Proof.
  intros B xs c.
  induction xs as [| x xs IH]; simpl.
  - reflexivity.
  - rewrite IH. lia.
Qed.

Fixpoint nat_vectors_below (arity bound : nat) : list (list nat) :=
  match arity with
  | 0 => [[]]
  | S arity' =>
      concat
        (map
          (fun i => map (fun xs => i :: xs)
            (nat_vectors_below arity' bound))
          (seq 0 bound))
  end.

Lemma nat_vectors_below_length :
  forall arity bound,
    length (nat_vectors_below arity bound) = Nat.pow bound arity.
Proof.
  induction arity as [| arity IH]; intros bound; simpl.
  - reflexivity.
  - rewrite length_concat_map.
    replace
      (map
        (fun i : nat =>
          length
            (map (fun xs : list nat => i :: xs)
              (nat_vectors_below arity bound)))
        (seq 0 bound))
      with
      (map
        (fun _ : nat => length (nat_vectors_below arity bound))
        (seq 0 bound)).
    2:{
      apply map_ext.
      intros i.
      rewrite map_length.
      reflexivity.
    }
    rewrite sum_nats_map_const.
    rewrite seq_length.
    rewrite IH.
    reflexivity.
Qed.

Lemma in_nat_vectors_below_length :
  forall xs arity bound,
    In xs (nat_vectors_below arity bound) ->
    length xs = arity.
Proof.
  intros xs arity.
  revert xs.
  induction arity as [| arity IH]; intros xs bound Hin; simpl in Hin.
  - destruct Hin as [Heq | []]. subst. reflexivity.
  - apply in_concat in Hin as [ys [Hys Hin]].
    apply in_map_iff in Hys as [i [Hys _Hi]].
    subst ys.
    apply in_map_iff in Hin as [tail [Hxs Htail]].
    subst xs.
    simpl.
    f_equal.
    now apply IH with (bound := bound).
Qed.

Lemma in_nat_vectors_below_nth :
  forall xs arity bound i x,
    In xs (nat_vectors_below arity bound) ->
    nth_error xs i = Some x ->
    x < bound.
Proof.
  intros xs arity.
  revert xs.
  induction arity as [| arity IH]; intros xs bound i x Hin Hnth;
    simpl in Hin.
  - destruct Hin as [Heq | []].
    subst.
    destruct i; simpl in Hnth; discriminate.
  - apply in_concat in Hin as [ys [Hys Hin]].
    apply in_map_iff in Hys as [head [Hys Hhead]].
    subst ys.
    apply in_map_iff in Hin as [tail [Hxs Htail]].
    subst xs.
    destruct i as [| i]; simpl in Hnth.
    + inversion Hnth; subst.
      apply in_seq in Hhead.
      lia.
    + eapply IH; eauto.
Qed.

Lemma nat_vectors_below_complete :
  forall xs arity bound,
    length xs = arity ->
    (forall i x, nth_error xs i = Some x -> x < bound) ->
    In xs (nat_vectors_below arity bound).
Proof.
  intros xs arity.
  revert xs.
  induction arity as [| arity IH]; intros xs bound Hlen Hnth; simpl.
  - destruct xs as [| x xs]; simpl in Hlen; try discriminate.
    left. reflexivity.
  - destruct xs as [| x xs]; simpl in Hlen; try discriminate.
    apply in_concat.
    exists (map (fun tail => x :: tail) (nat_vectors_below arity bound)).
    split.
    + apply in_map_iff.
      exists x.
      split; auto.
      apply in_seq.
      specialize (Hnth 0 x eq_refl).
      lia.
    + apply in_map_iff.
      exists xs.
      split; auto.
      apply IH.
      * lia.
      * intros i y Hy.
        apply (Hnth (S i) y).
        simpl. exact Hy.
Qed.

Definition pad_nat_vector (arity : nat) (xs : list nat) : list nat :=
  firstn arity (xs ++ repeat 0 arity).

Fixpoint pad_positive_nat_vector (arity : nat) (xs : list nat) : list nat :=
  match arity with
  | O => []
  | S arity' =>
      match xs with
      | [] => 0 :: pad_positive_nat_vector arity' []
      | x :: xs' => x :: pad_positive_nat_vector arity' xs'
      end
  end.

Lemma firstn_In :
  forall {B : Type} n (xs : list B) x,
    In x (firstn n xs) ->
    In x xs.
Proof.
  intros B n.
  induction n as [| n IH]; intros xs x Hin; simpl in Hin.
  - contradiction.
  - destruct xs as [| y xs]; simpl in *; auto.
    destruct Hin as [Heq | Hin].
    + subst. simpl. auto.
    + simpl. right. now apply IH.
Qed.

Lemma pad_nat_vector_length :
  forall arity xs,
    length xs <= arity ->
    length (pad_nat_vector arity xs) = arity.
Proof.
  intros arity xs Hlen.
  unfold pad_nat_vector.
  rewrite firstn_length.
  rewrite app_length.
  rewrite repeat_length.
  lia.
Qed.

Lemma pad_nat_vector_In_bound :
  forall arity bound xs x,
    0 < bound ->
    (forall y, In y xs -> y < bound) ->
    In x (pad_nat_vector arity xs) ->
    x < bound.
Proof.
  intros arity bound xs x Hbound Hxs Hin.
  unfold pad_nat_vector in Hin.
  apply firstn_In in Hin.
  apply in_app_iff in Hin as [Hin | Hin].
  - now apply Hxs.
  - apply repeat_spec in Hin. subst. exact Hbound.
Qed.

Lemma pad_nat_vector_nth_bound :
  forall arity bound xs i x,
    0 < bound ->
    (forall y, In y xs -> y < bound) ->
    nth_error (pad_nat_vector arity xs) i = Some x ->
    x < bound.
Proof.
  intros arity bound xs i x Hbound Hxs Hnth.
  apply pad_nat_vector_In_bound with (arity := arity) (xs := xs).
  - exact Hbound.
  - exact Hxs.
  - now apply nth_error_In with (n := i).
Qed.

Lemma pad_nat_vector_in_nat_vectors_below :
  forall arity bound xs,
    length xs <= arity ->
    0 < bound ->
    (forall y, In y xs -> y < bound) ->
    In (pad_nat_vector arity xs) (nat_vectors_below arity bound).
Proof.
  intros arity bound xs Hlen Hbound Hxs.
  apply nat_vectors_below_complete.
  - now apply pad_nat_vector_length.
  - intros i x Hnth.
    eapply pad_nat_vector_nth_bound; eauto.
Qed.

Lemma pad_positive_nat_vector_length :
  forall arity xs,
    length (pad_positive_nat_vector arity xs) = arity.
Proof.
  induction arity as [| arity IH]; intros xs; simpl.
  - reflexivity.
  - destruct xs as [| x xs]; simpl; now rewrite IH.
Qed.

Lemma pad_positive_nat_vector_nth_bound :
  forall arity bound xs i x,
    0 < bound ->
    (forall y, In y xs -> y < bound) ->
    nth_error (pad_positive_nat_vector arity xs) i = Some x ->
    x < bound.
Proof.
  induction arity as [| arity IH]; intros bound xs i x Hbound Hxs Hnth;
    simpl in Hnth.
  - destruct i; discriminate.
  - destruct xs as [| y ys]; destruct i as [| i]; simpl in Hnth.
    + injection Hnth as Hx. subst. exact Hbound.
    + eapply (IH bound [] i x).
      * exact Hbound.
      * intros z Hz. contradiction.
      * exact Hnth.
    + injection Hnth as Hx. subst.
      apply Hxs. simpl. auto.
    + eapply (IH bound ys i x).
      * exact Hbound.
      * intros z Hz. apply Hxs. simpl. auto.
      * exact Hnth.
Qed.

Lemma pad_positive_nat_vector_in_nat_vectors_below :
  forall arity bound xs,
    length xs <= arity ->
    0 < bound ->
    (forall x, In x xs -> x < bound) ->
    In (pad_positive_nat_vector arity xs) (nat_vectors_below arity bound).
Proof.
  intros arity bound xs _Hlen Hbound Hxs.
  apply nat_vectors_below_complete.
  - apply pad_positive_nat_vector_length.
  - intros i x Hnth.
    eapply pad_positive_nat_vector_nth_bound; eauto.
Qed.

Lemma pad_positive_nat_vector_eq :
  forall arity xs ys,
    length xs <= arity ->
    length ys <= arity ->
    (forall x, In x xs -> 0 < x) ->
    (forall y, In y ys -> 0 < y) ->
    pad_positive_nat_vector arity xs =
    pad_positive_nat_vector arity ys ->
    xs = ys.
Proof.
  induction arity as [| arity IH]; intros xs ys Hlenx Hleny Hposx Hposy Heq.
  - destruct xs as [| x xs]; simpl in Hlenx; try lia.
    destruct ys as [| y ys]; simpl in Hleny; try lia.
    reflexivity.
  - destruct xs as [| x xs]; destruct ys as [| y ys]; simpl in *.
    + reflexivity.
    + injection Heq as Hhead _.
      specialize (Hposy y (or_introl eq_refl)).
      lia.
    + injection Heq as Hhead _.
      specialize (Hposx x (or_introl eq_refl)).
      lia.
    + injection Heq as Hhead Htail.
      f_equal.
      * exact Hhead.
      * eapply IH.
        -- lia.
        -- lia.
        -- intros z Hz. apply Hposx. simpl. auto.
        -- intros z Hz. apply Hposy. simpl. auto.
        -- exact Htail.
Qed.

Lemma NoDup_map_cons_nat :
  forall (h : nat) (xs : list (list nat)),
    NoDup xs ->
    NoDup (map (fun ys => h :: ys) xs).
Proof.
  intros h xs Hnodup.
  induction Hnodup as [| x xs Hnotin Hnodup IH].
  - constructor.
  - simpl. constructor.
    + intros Hin.
      apply in_map_iff in Hin as [y [Heq Hy]].
      inversion Heq; subst.
      contradiction.
    + exact IH.
Qed.

Lemma NoDup_concat_cons_blocks :
  forall (heads : list nat) (tails : list (list nat)),
    NoDup heads ->
    NoDup tails ->
    NoDup
      (concat
        (map
          (fun h => map (fun xs => h :: xs) tails)
          heads)).
Proof.
  intros heads tails Hheads Htails.
  induction Hheads as [| h heads Hnotin Hnodup_heads IH].
  - constructor.
  - simpl.
    apply NoDup_app.
    repeat split.
    + now apply NoDup_map_cons_nat.
    + exact IH.
    + intros x Hleft Hright.
      apply in_map_iff in Hleft as [tail [Hx Htail]].
      subst x.
      apply in_concat in Hright as [block [Hblock Hmember]].
      apply in_map_iff in Hblock as [head [Hblock Hhead]].
      subst block.
      apply in_map_iff in Hmember as [tail' [Heq _Htail']].
      inversion Heq; subst.
      contradiction.
Qed.

Lemma nat_vectors_below_NoDup :
  forall arity bound,
    NoDup (nat_vectors_below arity bound).
Proof.
  induction arity as [| arity IH]; intros bound; simpl.
  - constructor.
    + intros [].
    + constructor.
  - apply NoDup_concat_cons_blocks.
    + apply seq_NoDup.
    + apply IH.
Qed.

Definition product_codes {B C : Type}
    (xs : list B)
    (ys : list C) : list (B * C) :=
  concat (map (fun x => map (fun y => (x, y)) ys) xs).

Lemma product_codes_length :
  forall {B C : Type} (xs : list B) (ys : list C),
    length (product_codes xs ys) = length xs * length ys.
Proof.
  intros B C xs ys.
  unfold product_codes.
  rewrite length_concat_map.
  replace
    (map (fun x : B => length (map (fun y : C => (x, y)) ys)) xs)
    with (map (fun _ : B => length ys) xs).
  2:{
    apply map_ext.
    intros x.
    rewrite map_length.
    reflexivity.
  }
  now rewrite sum_nats_map_const.
Qed.

Lemma product_codes_In :
  forall {B C : Type} (xs : list B) (ys : list C) x y,
    In x xs ->
    In y ys ->
    In (x, y) (product_codes xs ys).
Proof.
  intros B C xs ys x y Hx Hy.
  unfold product_codes.
  apply in_concat.
  exists (map (fun y => (x, y)) ys).
  split.
  - apply in_map_iff.
    exists x. split; reflexivity || assumption.
  - apply in_map_iff.
    exists y. split; reflexivity || assumption.
Qed.

Lemma NoDup_map_pair_right :
  forall {B C : Type} (x : B) (ys : list C),
    NoDup ys ->
    NoDup (map (fun y => (x, y)) ys).
Proof.
  intros B C x ys Hnodup.
  induction Hnodup as [| y ys Hnotin Hnodup IH].
  - constructor.
  - simpl. constructor.
    + intros Hin.
      apply in_map_iff in Hin as [y' [Heq Hy']].
      inversion Heq; subst.
      contradiction.
    + exact IH.
Qed.

Lemma product_codes_NoDup :
  forall {B C : Type} (xs : list B) (ys : list C),
    NoDup xs ->
    NoDup ys ->
    NoDup (product_codes xs ys).
Proof.
  intros B C xs ys Hxs Hys.
  unfold product_codes.
  induction Hxs as [| x xs Hnotin Hnodup_xs IH].
  - constructor.
  - simpl.
    apply NoDup_app.
    repeat split.
    + now apply NoDup_map_pair_right.
    + exact IH.
    + intros code Hleft Hright.
      apply in_map_iff in Hleft as [y [Hcode _Hy]].
      subst code.
      apply in_concat in Hright as [block [Hblock Hmember]].
      apply in_map_iff in Hblock as [x' [Hblock Hx']].
      subst block.
      apply in_map_iff in Hmember as [y' [Heq _Hy']].
      inversion Heq; subst.
      contradiction.
Qed.

Definition polynomial_signature_codes {Payload : Type}
    (payloads : list Payload)
    (arity bound : nat) : list (list nat * Payload) :=
  product_codes (nat_vectors_below arity bound) payloads.

Lemma polynomial_signature_codes_length :
  forall {Payload : Type} (payloads : list Payload) arity bound,
    length (polynomial_signature_codes payloads arity bound) =
      Nat.pow bound arity * length payloads.
Proof.
  intros Payload payloads arity bound.
  unfold polynomial_signature_codes.
  rewrite product_codes_length.
  now rewrite nat_vectors_below_length.
Qed.

Lemma polynomial_signature_codes_NoDup :
  forall {Payload : Type} (payloads : list Payload) arity bound,
    NoDup payloads ->
    NoDup (polynomial_signature_codes payloads arity bound).
Proof.
  intros Payload payloads arity bound Hpayloads.
  unfold polynomial_signature_codes.
  apply product_codes_NoDup.
  - apply nat_vectors_below_NoDup.
  - exact Hpayloads.
Qed.

Lemma polynomial_signature_codes_In :
  forall {Payload : Type} (payloads : list Payload) arity bound
    (positions : list nat) (payload : Payload),
    In positions (nat_vectors_below arity bound) ->
    In payload payloads ->
    In (positions, payload)
      (polynomial_signature_codes payloads arity bound).
Proof.
  intros Payload payloads arity bound positions payload Hpos Hpayload.
  unfold polynomial_signature_codes.
  now apply product_codes_In.
Qed.

Lemma NoDup_inj_length_le :
  forall {B C : Type} (xs : list B) (ys : list C) (f : B -> C),
    NoDup xs ->
    NoDup ys ->
    (forall x, In x xs -> In (f x) ys) ->
    (forall x y, In x xs -> In y xs -> f x = f y -> x = y) ->
    length xs <= length ys.
Proof.
  intros B C xs.
  induction xs as [| x xs IH]; intros ys f Hnodup_xs Hnodup_ys Hinto Hinj.
  - simpl. lia.
  - inversion Hnodup_xs as [| x' xs' Hnotin Hnodup_tail]; subst.
    assert (Hfx_in : In (f x) ys).
    {
      apply Hinto. simpl; auto.
    }
    destruct (in_split _ _ Hfx_in) as [ys1 [ys2 Hys]].
    subst ys.
    rewrite app_length. simpl.
    assert (Hnodup_without :
      NoDup (ys1 ++ ys2)).
    {
      apply NoDup_remove_1 with (a := f x).
      exact Hnodup_ys.
    }
    assert (Hinto_tail :
      forall y, In y xs -> In (f y) (ys1 ++ ys2)).
    {
      intros y Hy.
      pose proof (Hinto y (or_intror Hy)) as Hfy.
      rewrite in_app_iff in Hfy.
      simpl in Hfy.
      rewrite in_app_iff.
      destruct Hfy as [Hleft | [Heq | Hright]]; auto.
      exfalso.
      assert (x = y).
      {
        apply (Hinj x y); simpl; auto.
      }
      subst y. contradiction.
    }
    assert (Hinj_tail :
      forall y z, In y xs -> In z xs -> f y = f z -> y = z).
    {
      intros y z Hy Hz Heq.
      apply Hinj; simpl; auto.
    }
    pose proof (IH (ys1 ++ ys2) f Hnodup_tail Hnodup_without
      Hinto_tail Hinj_tail) as Hle.
    rewrite app_length in Hle.
    lia.
Qed.

Lemma length_le_from_index_injection :
  forall {C : Type} n (codes : list C) (encode : nat -> C),
    NoDup codes ->
    (forall i, i < n -> In (encode i) codes) ->
    (forall i j, i < n -> j < n -> encode i = encode j -> i = j) ->
    n <= length codes.
Proof.
  intros C n codes encode Hnodup Hinto Hinj.
  replace n with (length (seq 0 n)) by (rewrite seq_length; reflexivity).
  eapply NoDup_inj_length_le with
    (xs := seq 0 n) (ys := codes) (f := encode).
  - apply seq_NoDup.
  - exact Hnodup.
  - intros i Hi.
    apply Hinto.
    apply in_seq in Hi.
    lia.
  - intros i j Hi Hj Heq.
    apply Hinj; try (apply in_seq in Hi; lia);
      try (apply in_seq in Hj; lia); assumption.
Qed.

Lemma nth_error_In_lt :
  forall {B : Type} (xs : list B) i x,
    nth_error xs i = Some x ->
    In x xs /\ i < length xs.
Proof.
  intros B xs.
  induction xs as [| y xs IH]; intros i x Hnth.
  - destruct i; simpl in Hnth; discriminate.
  - destruct i as [| i]; simpl in Hnth.
    + inversion Hnth; subst. split; simpl; auto; lia.
    + destruct (IH i x Hnth) as [Hin Hlt].
      split; simpl; auto; lia.
Qed.

Lemma nth_error_exists_lt :
  forall {B : Type} (xs : list B) i,
    i < length xs ->
    exists x, nth_error xs i = Some x.
Proof.
  intros B xs.
  induction xs as [| x xs IH]; intros i Hlt.
  - simpl in Hlt. lia.
  - destruct i as [| i].
    + exists x. reflexivity.
    + simpl in Hlt.
      destruct (IH i) as [y Hy]; try lia.
      exists y. exact Hy.
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

  Definition word_in_alphabet (m : finite_nfa) (w : list A) : Prop :=
    Forall (fun a => In a (fnfa_alphabet m)) w.

  Definition fnfa_well_formed (m : finite_nfa) : Prop :=
    (forall q,
      In q (nfa_start (fnfa_base m)) ->
      In q (fnfa_states m)) /\
    (forall q a q',
      In q (fnfa_states m) ->
      In a (fnfa_alphabet m) ->
      In q' (nfa_step (fnfa_base m) q a) ->
      In q' (fnfa_states m)).

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

  Lemma path_from_app :
    forall (m : nfa) p u q v r,
      path_from m p u q ->
      path_from m q v r ->
      path_from m p (u ++ v) r.
  Proof.
    intros m p u q v r Hleft Hright.
    induction Hleft.
    - exact Hright.
    - simpl. eapply Path_cons; eauto.
  Qed.

  Inductive run_trace_from (m : nfa)
      : nfa_state m -> list A -> nfa_state m ->
        list (nfa_state m) -> Prop :=
  | Run_trace_nil :
      forall q,
        run_trace_from m q [] q [q]
  | Run_trace_cons :
      forall q a q' w qf trace,
        In q' (nfa_step m q a) ->
        run_trace_from m q' w qf trace ->
        run_trace_from m q (a :: w) qf (q :: trace).

  Lemma run_trace_from_path :
    forall (m : nfa) q w qf trace,
      run_trace_from m q w qf trace ->
      path_from m q w qf.
  Proof.
    intros m q w qf trace Htrace.
    induction Htrace.
    - constructor.
    - eapply Path_cons; eauto.
  Qed.

  Lemma run_trace_from_nth_prefix_path :
    forall (m : nfa) q w qf trace pos mid,
      run_trace_from m q w qf trace ->
      nth_error trace pos = Some mid ->
      exists u, path_from m q u mid.
  Proof.
    intros m q w qf trace pos mid Htrace.
    revert pos mid.
    induction Htrace as
      [q| q a q' w qf trace Hstep Htrace IH];
      intros pos mid Hnth.
    - destruct pos as [| pos]; simpl in Hnth.
      + inversion Hnth; subst. exists []. constructor.
      + induction pos; simpl in Hnth; discriminate.
    - destruct pos as [| pos]; simpl in Hnth.
      + inversion Hnth; subst. exists []. constructor.
      + destruct (IH pos mid Hnth) as [u Hpath].
        exists (a :: u).
        eapply Path_cons; eauto.
  Qed.

  Lemma run_trace_from_nth_suffix_path :
    forall (m : nfa) q w qf trace pos mid,
      run_trace_from m q w qf trace ->
      nth_error trace pos = Some mid ->
      exists v, path_from m mid v qf.
  Proof.
    intros m q w qf trace pos mid Htrace.
    revert pos mid.
    induction Htrace as
      [q| q a q' w qf trace Hstep Htrace IH];
      intros pos mid Hnth.
    - destruct pos as [| pos]; simpl in Hnth.
      + inversion Hnth; subst. exists []. constructor.
      + induction pos; simpl in Hnth; discriminate.
    - destruct pos as [| pos]; simpl in Hnth.
      + inversion Hnth; subst.
        exists (a :: w).
        eapply Path_cons; eauto.
        now apply run_trace_from_path with (trace := trace).
      + exact (IH pos mid Hnth).
  Qed.

  Lemma run_trace_from_length :
    forall (m : nfa) q w qf trace,
      run_trace_from m q w qf trace ->
      length trace = S (length w).
  Proof.
    intros m q w qf trace Htrace.
    induction Htrace; simpl; auto.
  Qed.

  Lemma run_trace_from_nonempty :
    forall (m : nfa) q w qf trace,
      run_trace_from m q w qf trace ->
      trace <> [].
  Proof.
    intros m q w qf trace Htrace.
    destruct Htrace; discriminate.
  Qed.

  Inductive run_choices_from (m : nfa)
      : nfa_state m -> list A -> list nat -> nfa_state m -> Prop :=
  | Run_choices_nil :
      forall q,
        run_choices_from m q [] [] q
  | Run_choices_cons :
      forall q a idx q' w choices qf,
        nth_error (nfa_step m q a) idx = Some q' ->
        run_choices_from m q' w choices qf ->
        run_choices_from m q (a :: w) (idx :: choices) qf.

  Lemma run_choices_from_path :
    forall (m : nfa) q w choices qf,
      run_choices_from m q w choices qf ->
      path_from m q w qf.
  Proof.
    intros m q w choices qf Hchoices.
    induction Hchoices.
    - constructor.
    - eapply Path_cons.
      + eapply nth_error_In. exact H.
      + exact IHHchoices.
  Qed.

  Lemma run_choices_from_length :
    forall (m : nfa) q w choices qf,
      run_choices_from m q w choices qf ->
      length choices = length w.
  Proof.
    intros m q w choices qf Hchoices.
    induction Hchoices; simpl; auto.
  Qed.

  Lemma nth_error_NoDup_eq :
    forall {B : Type} (xs : list B) i j x,
      NoDup xs ->
      nth_error xs i = Some x ->
      nth_error xs j = Some x ->
      i = j.
  Proof.
    intros B xs.
    induction xs as [| y ys IH]; intros i j x Hnodup Hi Hj;
      destruct i as [| i]; destruct j as [| j]; simpl in *;
      try discriminate; auto.
    - inversion Hi; subst y.
      inversion Hnodup as [| ? ? Hnotin _]; subst.
      exfalso. apply Hnotin.
      eapply nth_error_In. exact Hj.
    - inversion Hj; subst y.
      inversion Hnodup as [| ? ? Hnotin _]; subst.
      exfalso. apply Hnotin.
      eapply nth_error_In. exact Hi.
    - inversion Hnodup as [| ? ? _ Hnodup_tail]; subst.
      f_equal.
      eapply IH; eauto.
  Qed.

  Lemma run_choices_from_app :
    forall (m : nfa) q u cu mid v cv qf,
      run_choices_from m q u cu mid ->
      run_choices_from m mid v cv qf ->
      run_choices_from m q (u ++ v) (cu ++ cv) qf.
  Proof.
    intros m q u cu mid v cv qf Hleft Hright.
    induction Hleft as [q| q a idx q' u cu mid Hnth Hrun IH].
    - simpl. exact Hright.
    - simpl. eapply Run_choices_cons; eauto.
  Qed.

  Lemma run_choices_from_split :
    forall (m : nfa) q u v cu cv qf,
      run_choices_from m q (u ++ v) (cu ++ cv) qf ->
      length cu = length u ->
      exists mid,
        run_choices_from m q u cu mid /\
        run_choices_from m mid v cv qf.
  Proof.
    intros m q u.
    revert q.
    induction u as [| a u IH]; intros q v cu cv qf Hrun Hlen.
    - destruct cu as [| c cu]; simpl in Hlen; try discriminate.
      exists q. split; [constructor | exact Hrun].
    - destruct cu as [| idx cu]; simpl in Hlen; try discriminate.
      simpl in Hrun.
      inversion Hrun as
        [| q' a' idx' qnext w choices qf' Hnth Htail]; subst.
      destruct (IH qnext v cu cv qf Htail) as [mid [Hleft Hright]].
      { lia. }
      exists mid.
      split.
      + eapply Run_choices_cons; eauto.
      + exact Hright.
  Qed.

  Lemma run_choices_from_step_split :
    forall (m : nfa) q w choices qf pos a,
      run_choices_from m q w choices qf ->
      nth_error w pos = Some a ->
      exists u v cu idx cv p r,
        w = u ++ a :: v /\
        choices = cu ++ idx :: cv /\
        length u = pos /\
        run_choices_from m q u cu p /\
        nth_error (nfa_step m p a) idx = Some r /\
        run_choices_from m r v cv qf.
  Proof.
    intros m q w choices qf pos a Hrun.
    revert pos a.
    induction Hrun as
      [q| q b idx q' w choices qf Hstep Htail IH];
      intros pos a Hnth.
    - destruct pos; simpl in Hnth; discriminate.
    - destruct pos as [| pos].
      + simpl in Hnth. inversion Hnth; subst b.
        exists [], w, [], idx, choices, q, q'.
        repeat split; simpl; auto.
        constructor.
      + simpl in Hnth.
        destruct (IH pos a Hnth) as
          [u [v [cu [idx' [cv [p [r Hdata]]]]]]].
        destruct Hdata as
          [Hw [Hchoices [Hlen [Hleft [Hnth_step Hright]]]]].
        exists (b :: u), v, (idx :: cu), idx', cv, p, r.
        split.
        * simpl. now rewrite Hw.
        * split.
          -- simpl. now rewrite Hchoices.
          -- split.
             ++ simpl. lia.
             ++ split.
                ** eapply Run_choices_cons; eauto.
                ** split; assumption.
  Qed.

  Fixpoint replay_choices_from
      (m : nfa)
      (q : nfa_state m)
      (w : list A)
      (choices : list nat) : option (list (nfa_state m)) :=
    match w, choices with
    | [], [] => Some [q]
    | a :: w', idx :: choices' =>
        match nth_error (nfa_step m q a) idx with
        | Some q' =>
            match replay_choices_from m q' w' choices' with
            | Some trace => Some (q :: trace)
            | None => None
            end
        | None => None
        end
    | _, _ => None
    end.

  Lemma replay_choices_from_nonempty :
    forall (m : nfa) q w choices trace,
      replay_choices_from m q w choices = Some trace ->
      trace <> [].
  Proof.
    intros m q w.
    revert q.
    induction w as [| a w IH]; intros q choices trace Hreplay;
      destruct choices as [| idx choices]; simpl in Hreplay;
      try discriminate.
    - injection Hreplay as Htrace. subst. discriminate.
    - destruct (nth_error (nfa_step m q a) idx) as [q'|] eqn:Hnth;
        try discriminate.
      destruct (replay_choices_from m q' w choices) as [tail_trace|] eqn:Htail;
        try discriminate.
      injection Hreplay as Htrace.
      subst. discriminate.
  Qed.

  Lemma replay_choices_from_starts_with :
    forall (m : nfa) q w choices trace,
      replay_choices_from m q w choices = Some trace ->
      exists tail, trace = q :: tail.
  Proof.
    intros m q w.
    revert q.
    induction w as [| a w IH]; intros q choices trace Hreplay;
      destruct choices as [| idx choices]; simpl in Hreplay;
      try discriminate.
    - injection Hreplay as Htrace. subst. eauto.
    - destruct (nth_error (nfa_step m q a) idx) as [q'|] eqn:Hnth;
        try discriminate.
      destruct (replay_choices_from m q' w choices) as [tail_trace|] eqn:Htail;
        try discriminate.
      injection Hreplay as Htrace.
      subst. eauto.
  Qed.

  Lemma replay_choices_from_head_after_step :
    forall (m : nfa) q a w idx choices trace q',
      nth_error (nfa_step m q a) idx = Some q' ->
      replay_choices_from m q (a :: w) (idx :: choices) = Some trace ->
      exists tail_trace,
        trace = q :: tail_trace /\
        replay_choices_from m q' w choices = Some tail_trace /\
        tail_trace <> [].
  Proof.
    intros m q a w idx choices trace q' Hnth Hreplay.
    simpl in Hreplay.
    rewrite Hnth in Hreplay.
    destruct (replay_choices_from m q' w choices) as [tail_trace|] eqn:Htail;
      try discriminate.
    injection Hreplay as Htrace.
    subst trace.
    exists tail_trace.
    repeat split; auto.
    eapply replay_choices_from_nonempty. exact Htail.
  Qed.

  Lemma replay_choices_from_step_split :
    forall (m : nfa) q w choices qf trace pos a p r,
      run_choices_from m q w choices qf ->
      replay_choices_from m q w choices = Some trace ->
      nth_error trace pos = Some p ->
      nth_error trace (S pos) = Some r ->
      nth_error w pos = Some a ->
      exists u v cu idx cv,
        w = u ++ a :: v /\
        choices = cu ++ idx :: cv /\
        length u = pos /\
        run_choices_from m q u cu p /\
        nth_error (nfa_step m p a) idx = Some r /\
        run_choices_from m r v cv qf.
  Proof.
    intros m q w.
    revert q.
    induction w as [| b w IH];
      intros q choices qf trace pos a p r
        Hrun Hreplay Htrace_p Htrace_r Hword.
    - destruct pos; simpl in Hword; discriminate.
    - destruct choices as [| idx choices]; simpl in Hreplay;
        try discriminate.
      inversion Hrun as
        [| q_run b_run idx_run q' w_run choices_run qf_run
           Hstep Htail]; subst.
      rewrite Hstep in Hreplay.
      destruct
        (replay_choices_from m q' w choices)
        as [tail_trace|] eqn:Htail_replay;
        try discriminate.
      inversion Hreplay; subst trace; clear Hreplay.
      destruct pos as [| pos].
      + simpl in Hword. inversion Hword; subst b.
        simpl in Htrace_p, Htrace_r.
        inversion Htrace_p; subst p.
        destruct
          (replay_choices_from_starts_with
            m q' w choices tail_trace Htail_replay)
          as [tail_tail Htail_eq].
        subst tail_trace.
        simpl in Htrace_r.
        inversion Htrace_r; subst r.
        exists [], w, [], idx, choices.
        repeat split; simpl; auto.
        constructor.
      + simpl in Hword, Htrace_p, Htrace_r.
        destruct
          (IH q' choices qf tail_trace pos a p r
             Htail Htail_replay Htrace_p Htrace_r Hword)
          as [u [v [cu [idx' [cv Hdata]]]]].
        destruct Hdata as
          [Hw [Hchoices [Hlen [Hleft [Hnth_step Hright]]]]].
        exists (b :: u), v, (idx :: cu), idx', cv.
        split.
        * simpl. now rewrite Hw.
        * split.
          -- simpl. now rewrite Hchoices.
          -- split.
             ++ simpl. lia.
             ++ split.
                ** eapply Run_choices_cons; eauto.
                ** split; assumption.
  Qed.

  Lemma replay_choices_from_unique_with_nodup_steps :
    forall (m : nfa),
      (forall q a, NoDup (nfa_step m q a)) ->
      forall q w c1 c2 trace,
        length c1 = length w ->
        length c2 = length w ->
        replay_choices_from m q w c1 = Some trace ->
        replay_choices_from m q w c2 = Some trace ->
        c1 = c2.
  Proof.
    intros m Hnodup q w.
    revert q.
    induction w as [| a w IH]; intros q c1 c2 trace Hlen1 Hlen2 Hr1 Hr2.
    - destruct c1 as [| x c1]; simpl in Hlen1; try discriminate.
      destruct c2 as [| y c2]; simpl in Hlen2; try discriminate.
      reflexivity.
    - destruct c1 as [| idx1 c1]; simpl in Hlen1; try discriminate.
      destruct c2 as [| idx2 c2]; simpl in Hlen2; try discriminate.
      simpl in Hr1, Hr2.
      destruct (nth_error (nfa_step m q a) idx1) as [q1|] eqn:Hnth1;
        try discriminate.
      destruct (nth_error (nfa_step m q a) idx2) as [q2|] eqn:Hnth2;
        try discriminate.
      destruct (replay_choices_from m q1 w c1) as [trace1|] eqn:Htail1;
        try discriminate.
      destruct (replay_choices_from m q2 w c2) as [trace2|] eqn:Htail2;
        try discriminate.
      injection Hr1 as Htrace1.
      injection Hr2 as Htrace2.
      subst trace.
      injection Htrace2 as Htrace_eq.
      subst trace2.
      assert (Hqeq : q1 = q2).
      {
        pose proof
          (replay_choices_from_nonempty m q1 w c1 trace1 Htail1)
          as Hnonempty1.
        pose proof
          (replay_choices_from_nonempty m q2 w c2 trace1 Htail2)
          as Hnonempty2.
        destruct trace1 as [| h t]; try contradiction.
        simpl in Htail1, Htail2.
        destruct w as [| b w']; simpl in Htail1, Htail2.
        - destruct c1 as [| z c1]; try discriminate.
          destruct c2 as [| z c2]; try discriminate.
          injection Htail1 as Hh1.
          injection Htail2 as Hh2.
          subst. reflexivity.
        - destruct c1 as [| z1 c1]; try discriminate.
          destruct c2 as [| z2 c2]; try discriminate.
          destruct (nth_error (nfa_step m q1 b) z1) as [r1|];
            try discriminate.
          destruct (nth_error (nfa_step m q2 b) z2) as [r2|];
            try discriminate.
          destruct (replay_choices_from m r1 w' c1); try discriminate.
          destruct (replay_choices_from m r2 w' c2); try discriminate.
          injection Htail1 as Hhead1.
          injection Htail2 as Hhead2.
          subst. reflexivity.
      }
      subst q2.
      assert (Hidx : idx1 = idx2).
      {
        eapply nth_error_NoDup_eq; eauto.
      }
      subst idx2.
      f_equal.
      eapply IH with (trace := trace1); eauto; lia.
  Qed.

  Lemma replay_choices_from_run_choices :
    forall (m : nfa) q w choices qf,
      run_choices_from m q w choices qf ->
      exists trace,
        replay_choices_from m q w choices = Some trace /\
        run_trace_from m q w qf trace.
  Proof.
    intros m q w choices qf Hchoices.
    induction Hchoices as [q| q a idx q' w choices qf Hnth Hrun IH].
    - exists [q]. split; simpl; constructor.
    - destruct IH as [trace [Hreplay Htrace]].
      exists (q :: trace).
      simpl. rewrite Hnth. rewrite Hreplay.
      split; [reflexivity |].
      eapply Run_trace_cons.
      + eapply nth_error_In. exact Hnth.
      + exact Htrace.
  Qed.

  Lemma replay_choices_from_run_choices_length :
    forall (m : nfa) q w choices qf trace,
      run_choices_from m q w choices qf ->
      replay_choices_from m q w choices = Some trace ->
      length trace = S (length w).
  Proof.
    intros m q w choices qf trace Hchoices Hreplay.
    destruct (replay_choices_from_run_choices m q w choices qf Hchoices)
      as [trace' [Hreplay' Htrace]].
    rewrite Hreplay in Hreplay'. injection Hreplay' as Htrace_eq.
    subst trace'.
    now apply run_trace_from_length in Htrace.
  Qed.

  Lemma last_nonempty_irrelevant :
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

  Lemma fnfa_well_formed_path_end :
    forall (m : finite_nfa) p w q,
      fnfa_well_formed m ->
      In p (fnfa_states m) ->
      word_in_alphabet m w ->
      path_from (fnfa_base m) p w q ->
      In q (fnfa_states m).
  Proof.
    intros m p w q [_ Hstep] Hp Hall Hpath.
    induction Hpath.
    - exact Hp.
    - inversion Hall as [| a' w' Ha Hall_tail]; subst.
      apply IHHpath.
      + eapply Hstep; eauto.
      + exact Hall_tail.
  Qed.

  Lemma fnfa_well_formed_start_path_end :
    forall (m : finite_nfa) p w q,
      fnfa_well_formed m ->
      In p (nfa_start (fnfa_base m)) ->
      word_in_alphabet m w ->
      path_from (fnfa_base m) p w q ->
      In q (fnfa_states m).
  Proof.
    intros m p w q Hwf Hstart Hall Hpath.
    destruct Hwf as [Hstarts Hstep].
    eapply fnfa_well_formed_path_end.
    - split; eauto.
    - apply Hstarts. exact Hstart.
    - exact Hall.
    - exact Hpath.
  Qed.

  Lemma run_trace_from_states :
    forall (m : finite_nfa) q w qf trace,
      fnfa_well_formed m ->
      In q (fnfa_states m) ->
      word_in_alphabet m w ->
      run_trace_from (fnfa_base m) q w qf trace ->
      Forall (fun p => In p (fnfa_states m)) trace.
  Proof.
    intros m q w qf trace Hwf Hq Hall Htrace.
    revert Hq Hall.
    induction Htrace as [q| q a q' w qf trace Hstep Htail IH];
      intros Hq Hall.
    - constructor; auto.
    - inversion Hall as [| a' w' Ha Hall_tail]; subst.
      destruct Hwf as [Hstarts Hstep_wf].
      assert (Hq' : In q' (fnfa_states m)).
      {
        eapply Hstep_wf; eauto.
      }
      constructor.
      + exact Hq.
      + apply IH.
        * exact Hq'.
        * exact Hall_tail.
  Qed.

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

  Definition fnfa_trim (m : finite_nfa) : Prop :=
    forall q,
      In q (fnfa_states m) ->
      useful_state (fnfa_base m) q.

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

  Fixpoint accepting_run_endpoints_from
      (m : finite_nfa)
      (q : nfa_state (fnfa_base m))
      (w : list A) : list (nfa_state (fnfa_base m)) :=
    match w with
    | [] =>
        if nfa_final (fnfa_base m) q then [q] else []
    | a :: w' =>
        concat
          (map
             (fun q' => accepting_run_endpoints_from m q' w')
             (nfa_step (fnfa_base m) q a))
    end.

  Lemma accepting_run_endpoints_from_length :
    forall (m : finite_nfa) q w,
      length (accepting_run_endpoints_from m q w) =
        accepting_runs_from (fnfa_base m) q w.
  Proof.
    intros m q w.
    revert q.
    induction w as [| a w IH]; intros q; simpl.
    - destruct (nfa_final (fnfa_base m) q); reflexivity.
    - rewrite length_concat_map.
      generalize (nfa_step (fnfa_base m) q a).
      intros qs.
      induction qs as [| q' qs IHqs]; simpl.
      + reflexivity.
      + rewrite IH. rewrite IHqs. reflexivity.
  Qed.

  Lemma accepting_run_endpoints_from_In :
    forall (m : finite_nfa) q w r,
      In r (accepting_run_endpoints_from m q w) ->
      path_from (fnfa_base m) q w r /\
      nfa_final (fnfa_base m) r = true.
  Proof.
    intros m q w.
    revert q.
    induction w as [| a w IH]; intros q r Hin; simpl in Hin.
    - destruct (nfa_final (fnfa_base m) q) eqn:Hfinal; simpl in Hin;
        try contradiction.
      destruct Hin as [Hr | Hin]; try contradiction.
      subst r. split; constructor || assumption.
    - apply in_concat in Hin as [rs [Hrs Hr]].
      apply in_map_iff in Hrs as [q' [Hrs Hq']].
      subst rs.
      destruct (IH q' r Hr) as [Hpath Hfinal].
      split; auto.
      eapply Path_cons; eauto.
  Qed.

  Definition ambiguity_of_word (m : nfa) (w : list A) : nat :=
    sum_nats (map (fun q => accepting_runs_from m q w) (nfa_start m)).

  Definition accepting_run_endpoints
      (m : finite_nfa)
      (w : list A) : list (nfa_state (fnfa_base m)) :=
    concat
      (map
         (fun q => accepting_run_endpoints_from m q w)
         (nfa_start (fnfa_base m))).

  Lemma accepting_run_endpoints_length :
    forall (m : finite_nfa) w,
      length (accepting_run_endpoints m w) =
        ambiguity_of_word (fnfa_base m) w.
  Proof.
    intros m w.
    unfold accepting_run_endpoints, ambiguity_of_word.
    rewrite length_concat_map.
    generalize (nfa_start (fnfa_base m)).
    intros qs.
    induction qs as [| q qs IHqs]; simpl.
    - reflexivity.
    - rewrite accepting_run_endpoints_from_length.
      rewrite IHqs. reflexivity.
  Qed.

  Lemma accepting_run_endpoints_In :
    forall (m : finite_nfa) w r,
      In r (accepting_run_endpoints m w) ->
      exists q0,
        In q0 (nfa_start (fnfa_base m)) /\
        path_from (fnfa_base m) q0 w r /\
        nfa_final (fnfa_base m) r = true.
  Proof.
    intros m w r Hin.
    unfold accepting_run_endpoints in Hin.
    apply in_concat in Hin as [rs [Hrs Hr]].
    apply in_map_iff in Hrs as [q0 [Hrs Hq0]].
    subst rs.
    destruct (accepting_run_endpoints_from_In m q0 w r Hr)
      as [Hpath Hfinal].
    exists q0. repeat split; assumption.
  Qed.

  Lemma accepting_run_endpoints_from_In_states :
    forall (m : finite_nfa) q w r,
      fnfa_well_formed m ->
      In q (fnfa_states m) ->
      word_in_alphabet m w ->
      In r (accepting_run_endpoints_from m q w) ->
      In r (fnfa_states m).
  Proof.
    intros m q w r Hwf Hq Hall Hin.
    destruct (accepting_run_endpoints_from_In m q w r Hin)
      as [Hpath _].
    eapply fnfa_well_formed_path_end; eauto.
  Qed.

  Lemma accepting_run_endpoints_In_states :
    forall (m : finite_nfa) w r,
      fnfa_well_formed m ->
      word_in_alphabet m w ->
      In r (accepting_run_endpoints m w) ->
      In r (fnfa_states m).
  Proof.
    intros m w r Hwf Hall Hin.
    destruct (accepting_run_endpoints_In m w r Hin)
      as [q0 [Hstart [Hpath _]]].
    eapply fnfa_well_formed_start_path_end; eauto.
  Qed.

  Fixpoint accepting_run_traces_from
      (m : finite_nfa)
      (q : nfa_state (fnfa_base m))
      (w : list A) : list (list (nfa_state (fnfa_base m))) :=
    match w with
    | [] =>
        if nfa_final (fnfa_base m) q then [[q]] else []
    | a :: w' =>
        concat
          (map
             (fun q' =>
                map
                  (fun trace => q :: trace)
                  (accepting_run_traces_from m q' w'))
             (nfa_step (fnfa_base m) q a))
    end.

  Lemma accepting_run_traces_from_length :
    forall (m : finite_nfa) q w,
      length (accepting_run_traces_from m q w) =
        accepting_runs_from (fnfa_base m) q w.
  Proof.
    intros m q w.
    revert q.
    induction w as [| a w IH]; intros q; simpl.
    - destruct (nfa_final (fnfa_base m) q); reflexivity.
    - rewrite length_concat_map.
      generalize (nfa_step (fnfa_base m) q a).
      intros qs.
      induction qs as [| q' qs IHqs]; simpl.
      + reflexivity.
      + rewrite map_length.
        rewrite IH.
        rewrite IHqs.
        reflexivity.
  Qed.

  Definition accepting_run_traces
      (m : finite_nfa)
      (w : list A) : list (list (nfa_state (fnfa_base m))) :=
    concat
      (map
         (fun q => accepting_run_traces_from m q w)
         (nfa_start (fnfa_base m))).

  Lemma accepting_run_traces_length :
    forall (m : finite_nfa) w,
      length (accepting_run_traces m w) =
        ambiguity_of_word (fnfa_base m) w.
  Proof.
    intros m w.
    unfold accepting_run_traces, ambiguity_of_word.
    rewrite length_concat_map.
    generalize (nfa_start (fnfa_base m)).
    intros qs.
    induction qs as [| q qs IHqs]; simpl.
    - reflexivity.
    - rewrite accepting_run_traces_from_length.
      rewrite IHqs. reflexivity.
  Qed.

  Lemma accepting_run_traces_from_In_trace :
    forall (m : finite_nfa) q w trace,
      In trace (accepting_run_traces_from m q w) ->
      exists qf,
        run_trace_from (fnfa_base m) q w qf trace /\
        nfa_final (fnfa_base m) qf = true.
  Proof.
    intros m q w.
    revert q.
    induction w as [| a w IH]; intros q trace Hin; simpl in Hin.
    - destruct (nfa_final (fnfa_base m) q) eqn:Hfinal; simpl in Hin;
        try contradiction.
      destruct Hin as [Htrace | []].
      subst trace.
      exists q. split; constructor || exact Hfinal.
    - apply in_concat in Hin as [traces [Htraces Htrace_in]].
      apply in_map_iff in Htraces as [q' [Htraces Hq']].
      subst traces.
      apply in_map_iff in Htrace_in as [tail [Htrace Htail]].
      subst trace.
      destruct (IH q' tail Htail) as [qf [Hrun Hfinal]].
      exists qf.
      split; auto.
      eapply Run_trace_cons; eauto.
  Qed.

  Lemma accepting_run_traces_In_trace :
    forall (m : finite_nfa) w trace,
      In trace (accepting_run_traces m w) ->
      exists q0 qf,
        In q0 (nfa_start (fnfa_base m)) /\
        run_trace_from (fnfa_base m) q0 w qf trace /\
        nfa_final (fnfa_base m) qf = true.
  Proof.
    intros m w trace Hin.
    unfold accepting_run_traces in Hin.
    apply in_concat in Hin as [traces [Htraces Htrace]].
    apply in_map_iff in Htraces as [q0 [Htraces Hq0]].
    subst traces.
    destruct (accepting_run_traces_from_In_trace m q0 w trace Htrace)
      as [qf [Hrun Hfinal]].
    exists q0, qf. repeat split; assumption.
  Qed.

  Lemma accepting_run_traces_In_path :
    forall (m : finite_nfa) w trace,
      In trace (accepting_run_traces m w) ->
      exists q0 qf,
        In q0 (nfa_start (fnfa_base m)) /\
        path_from (fnfa_base m) q0 w qf /\
        nfa_final (fnfa_base m) qf = true /\
        length trace = S (length w).
  Proof.
    intros m w trace Hin.
    destruct (accepting_run_traces_In_trace m w trace Hin)
      as [q0 [qf [Hstart [Hrun Hfinal]]]].
    exists q0, qf.
    repeat split; try assumption.
    - now apply run_trace_from_path with (trace := trace).
    - now apply run_trace_from_length in Hrun.
  Qed.

  Fixpoint accepting_run_choices_from
      (m : finite_nfa)
      (q : nfa_state (fnfa_base m))
      (w : list A) : list (list nat) :=
    match w with
    | [] =>
        if nfa_final (fnfa_base m) q then [[]] else []
    | a :: w' =>
        let fix choices_from_successors
            (idx : nat)
            (qs : list (nfa_state (fnfa_base m))) : list (list nat) :=
          match qs with
          | [] => []
          | q' :: qs' =>
              map
                (fun choices => idx :: choices)
                (accepting_run_choices_from m q' w') ++
              choices_from_successors (S idx) qs'
          end in
        choices_from_successors 0 (nfa_step (fnfa_base m) q a)
    end.

  Lemma accepting_run_choices_from_successors_length :
    forall (m : finite_nfa) w idx qs,
      (forall q,
        length (accepting_run_choices_from m q w) =
          accepting_runs_from (fnfa_base m) q w) ->
      length
        ((fix choices_from_successors
            (idx : nat)
            (qs : list (nfa_state (fnfa_base m))) : list (list nat) :=
          match qs with
          | [] => []
          | q' :: qs' =>
              map
                (fun choices => idx :: choices)
                (accepting_run_choices_from m q' w) ++
              choices_from_successors (S idx) qs'
          end) idx qs) =
        sum_nats
          (map
             (fun q => accepting_runs_from (fnfa_base m) q w)
             qs).
  Proof.
    intros m w idx qs Hlen.
    revert idx.
    induction qs as [| q qs IHqs]; intros idx; simpl.
    - reflexivity.
    - rewrite length_app.
      rewrite map_length.
      rewrite Hlen.
      rewrite IHqs.
      reflexivity.
  Qed.

  Lemma accepting_run_choices_from_length :
    forall (m : finite_nfa) q w,
      length (accepting_run_choices_from m q w) =
        accepting_runs_from (fnfa_base m) q w.
  Proof.
    intros m q w.
    revert q.
    induction w as [| a w IH]; intros q; simpl.
    - destruct (nfa_final (fnfa_base m) q); reflexivity.
    - apply accepting_run_choices_from_successors_length.
      intros q'. apply IH.
  Qed.

  Definition accepting_run_choices
      (m : finite_nfa)
      (w : list A) : list (list nat) :=
    concat
      (map
         (fun q => accepting_run_choices_from m q w)
         (nfa_start (fnfa_base m))).

  Lemma accepting_run_choices_length :
    forall (m : finite_nfa) w,
      length (accepting_run_choices m w) =
        ambiguity_of_word (fnfa_base m) w.
  Proof.
    intros m w.
    unfold accepting_run_choices, ambiguity_of_word.
    rewrite length_concat_map.
    generalize (nfa_start (fnfa_base m)).
    intros qs.
    induction qs as [| q qs IHqs]; simpl.
    - reflexivity.
    - rewrite accepting_run_choices_from_length.
      rewrite IHqs. reflexivity.
  Qed.

  Lemma accepting_run_choices_from_In_length :
    forall (m : finite_nfa) q w choices,
      In choices (accepting_run_choices_from m q w) ->
      length choices = length w.
  Proof.
    intros m q w.
    revert q.
    induction w as [| a w IH]; intros q choices Hin; simpl in Hin.
    - destruct (nfa_final (fnfa_base m) q); simpl in Hin;
        try contradiction.
      destruct Hin as [Hchoices | []].
      subst choices. reflexivity.
    - assert (Hsucc :
        forall idx qs choices,
          In choices
            ((fix choices_from_successors
                (idx : nat)
                (qs : list (nfa_state (fnfa_base m))) : list (list nat) :=
              match qs with
              | [] => []
              | q' :: qs' =>
                  map
                    (fun choices => idx :: choices)
                    (accepting_run_choices_from m q' w) ++
                  choices_from_successors (S idx) qs'
              end) idx qs) ->
          length choices = S (length w)).
      {
        intros idx qs.
        revert idx.
        induction qs as [| q' qs IHqs]; intros idx choice Hchoice;
          simpl in Hchoice; try contradiction.
        apply in_app_iff in Hchoice as [Hchoice | Hchoice].
        - apply in_map_iff in Hchoice as [tail [Hchoice Htail]].
          subst choice.
          simpl. f_equal.
          now apply (IH q').
        - now apply IHqs in Hchoice.
      }
      now apply Hsucc in Hin.
  Qed.

  Lemma accepting_run_choices_In_length :
    forall (m : finite_nfa) w choices,
      In choices (accepting_run_choices m w) ->
      length choices = length w.
  Proof.
    intros m w choices Hin.
    unfold accepting_run_choices in Hin.
    apply in_concat in Hin as [choices_from_q [Hchoices_from_q Hchoices]].
    apply in_map_iff in Hchoices_from_q as [q [Hchoices_from_q _Hq]].
    subst choices_from_q.
    now apply accepting_run_choices_from_In_length in Hchoices.
  Qed.

  Lemma accepting_run_choices_from_In_choices :
    forall (m : finite_nfa) q w choices,
      In choices (accepting_run_choices_from m q w) ->
      exists qf,
        run_choices_from (fnfa_base m) q w choices qf /\
        nfa_final (fnfa_base m) qf = true.
  Proof.
    intros m q w.
    revert q.
    induction w as [| a w IH]; intros q choices Hin; simpl in Hin.
    - destruct (nfa_final (fnfa_base m) q) eqn:Hfinal; simpl in Hin;
        try contradiction.
      destruct Hin as [Hchoices | []].
      subst choices.
      exists q. split; constructor || exact Hfinal.
    - assert (Hsucc :
        forall idx qs choices,
          In choices
            ((fix choices_from_successors
                (idx : nat)
                (qs : list (nfa_state (fnfa_base m))) : list (list nat) :=
              match qs with
              | [] => []
              | q' :: qs' =>
                  map
                    (fun choices => idx :: choices)
                    (accepting_run_choices_from m q' w) ++
                  choices_from_successors (S idx) qs'
              end) idx qs) ->
          exists offset q' tail qf,
            choices = (idx + offset) :: tail /\
            nth_error qs offset = Some q' /\
            run_choices_from (fnfa_base m) q' w tail qf /\
            nfa_final (fnfa_base m) qf = true).
      {
        intros idx qs.
        revert idx.
        induction qs as [| q' qs IHqs]; intros idx choice Hchoice;
          simpl in Hchoice; try contradiction.
        apply in_app_iff in Hchoice as [Hchoice | Hchoice].
        - apply in_map_iff in Hchoice as [tail [Hchoice_eq Htail]].
          subst choice.
          destruct (IH q' tail Htail) as [qf [Hrun Hfinal]].
          exists 0, q', tail, qf.
          simpl.
          repeat split.
          + f_equal. lia.
          + exact Hrun.
          + exact Hfinal.
        - destruct (IHqs (S idx) choice Hchoice)
            as [offset [q'' [tail [qf [Hchoice_eq [Hnth [Hrun Hfinal]]]]]]].
          exists (S offset), q'', tail, qf.
          simpl.
          repeat split; try assumption.
          rewrite Hchoice_eq.
          f_equal. lia.
      }
      destruct (Hsucc 0 (nfa_step (fnfa_base m) q a) choices Hin)
        as [offset [q' [tail [qf [Hchoices [Hnth [Hrun Hfinal]]]]]]].
      subst choices.
      simpl.
      exists qf.
      split; auto.
      eapply Run_choices_cons.
      + exact Hnth.
      + exact Hrun.
  Qed.

  Lemma accepting_run_choices_In_choices :
    forall (m : finite_nfa) w choices,
      In choices (accepting_run_choices m w) ->
      exists q0 qf,
        In q0 (nfa_start (fnfa_base m)) /\
        run_choices_from (fnfa_base m) q0 w choices qf /\
        nfa_final (fnfa_base m) qf = true.
  Proof.
    intros m w choices Hin.
    unfold accepting_run_choices in Hin.
    apply in_concat in Hin as [choices_from_q [Hchoices_from_q Hchoices]].
    apply in_map_iff in Hchoices_from_q as [q0 [Hchoices_from_q Hq0]].
    subst choices_from_q.
    destruct (accepting_run_choices_from_In_choices m q0 w choices Hchoices)
      as [qf [Hrun Hfinal]].
    exists q0, qf. repeat split; assumption.
  Qed.

  Definition accepting_run_full_choices
      (m : finite_nfa)
      (w : list A) : list (list nat) :=
    (fix choices_from_starts
        (idx : nat)
        (qs : list (nfa_state (fnfa_base m))) : list (list nat) :=
      match qs with
      | [] => []
      | q :: qs' =>
          map
            (fun choices => idx :: choices)
            (accepting_run_choices_from m q w) ++
          choices_from_starts (S idx) qs'
      end) 0 (nfa_start (fnfa_base m)).

  Lemma accepting_run_full_choices_length :
    forall (m : finite_nfa) w,
      length (accepting_run_full_choices m w) =
        ambiguity_of_word (fnfa_base m) w.
  Proof.
    intros m w.
    unfold accepting_run_full_choices, ambiguity_of_word.
    assert (Hstarts :
      forall idx qs,
        length
          ((fix choices_from_starts
              (idx0 : nat)
              (qs0 : list (nfa_state (fnfa_base m))) : list (list nat) :=
            match qs0 with
            | [] => []
            | q :: qs' =>
                map
                  (fun choices => idx0 :: choices)
                  (accepting_run_choices_from m q w) ++
                choices_from_starts (S idx0) qs'
            end) idx qs) =
        sum_nats
          (map
             (fun q => accepting_runs_from (fnfa_base m) q w)
             qs)).
    {
      intros idx qs.
      revert idx.
      induction qs as [| q qs IHqs]; intros idx; simpl.
      - reflexivity.
      - rewrite length_app.
        rewrite map_length.
        rewrite accepting_run_choices_from_length.
        rewrite IHqs.
        reflexivity.
    }
    apply Hstarts.
  Qed.

  Lemma accepting_run_full_choices_In_length :
    forall (m : finite_nfa) w choices,
      In choices (accepting_run_full_choices m w) ->
      length choices = S (length w).
  Proof.
    intros m w choices Hin.
    unfold accepting_run_full_choices in Hin.
    assert (Hstarts :
      forall idx qs,
        In choices
          ((fix choices_from_starts
              (idx0 : nat)
              (qs0 : list (nfa_state (fnfa_base m))) : list (list nat) :=
            match qs0 with
            | [] => []
            | q :: qs' =>
                map
                  (fun choices => idx0 :: choices)
                  (accepting_run_choices_from m q w) ++
                choices_from_starts (S idx0) qs'
            end) idx qs) ->
        length choices = S (length w)).
    {
      intros idx qs.
      revert idx.
      induction qs as [| q qs IHqs]; intros idx Hchoices; simpl in Hchoices;
        try contradiction.
      apply in_app_iff in Hchoices as [Hchoices | Hchoices].
      - apply in_map_iff in Hchoices as [tail [Hchoices Htail]].
        subst choices.
        simpl. f_equal.
        now apply accepting_run_choices_from_In_length with (m := m) (q := q).
      - now apply IHqs with (idx := S idx).
    }
    exact (Hstarts 0 (nfa_start (fnfa_base m)) Hin).
  Qed.

  Lemma accepting_run_full_choices_In_choices :
    forall (m : finite_nfa) w choices,
      In choices (accepting_run_full_choices m w) ->
      exists start_idx q0 tail qf,
        choices = start_idx :: tail /\
        nth_error (nfa_start (fnfa_base m)) start_idx = Some q0 /\
        run_choices_from (fnfa_base m) q0 w tail qf /\
        nfa_final (fnfa_base m) qf = true.
  Proof.
    intros m w choices Hin.
    unfold accepting_run_full_choices in Hin.
    assert (Hstarts :
      forall idx qs,
        In choices
          ((fix choices_from_starts
              (idx0 : nat)
              (qs0 : list (nfa_state (fnfa_base m))) : list (list nat) :=
            match qs0 with
            | [] => []
            | q :: qs' =>
                map
                  (fun choices => idx0 :: choices)
                  (accepting_run_choices_from m q w) ++
                choices_from_starts (S idx0) qs'
            end) idx qs) ->
        exists offset q0 tail qf,
          choices = (idx + offset) :: tail /\
          nth_error qs offset = Some q0 /\
          run_choices_from (fnfa_base m) q0 w tail qf /\
          nfa_final (fnfa_base m) qf = true).
    {
      intros idx qs.
      revert idx.
      induction qs as [| q qs IHqs]; intros idx Hchoices; simpl in Hchoices;
        try contradiction.
      apply in_app_iff in Hchoices as [Hchoices | Hchoices].
      - apply in_map_iff in Hchoices as [tail [Hchoices Htail]].
        subst choices.
        destruct (accepting_run_choices_from_In_choices m q w tail Htail)
          as [qf [Hrun Hfinal]].
        exists 0, q, tail, qf.
        simpl.
        repeat split.
        + f_equal. lia.
        + exact Hrun.
        + exact Hfinal.
      - destruct (IHqs (S idx) Hchoices)
          as [offset [q0 [tail [qf [Hchoices_eq [Hnth [Hrun Hfinal]]]]]]].
        exists (S offset), q0, tail, qf.
        simpl.
        repeat split; try assumption.
        rewrite Hchoices_eq.
        f_equal. lia.
    }
    destruct (Hstarts 0 (nfa_start (fnfa_base m)) Hin)
      as [start_idx [q0 [tail [qf [Hchoices [Hnth [Hrun Hfinal]]]]]]].
    exists start_idx, q0, tail, qf.
    repeat split; assumption.
  Qed.

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

  Fixpoint run_choices_between
      (m : finite_nfa)
      (q : nfa_state (fnfa_base m))
      (w : list A)
      (r : nfa_state (fnfa_base m)) : list (list nat) :=
    match w with
    | [] =>
        if fnfa_state_eqb m q r then [[]] else []
    | a :: w' =>
        (fix choices_from_successors
            (idx : nat)
            (qs : list (nfa_state (fnfa_base m))) : list (list nat) :=
          match qs with
          | [] => []
          | q' :: qs' =>
              map
                (fun choices => idx :: choices)
                (run_choices_between m q' w' r) ++
              choices_from_successors (S idx) qs'
          end) 0 (nfa_step (fnfa_base m) q a)
    end.

  Lemma run_choices_between_length :
    forall (m : finite_nfa) q w r,
      length (run_choices_between m q w r) = runs_between m q w r.
  Proof.
    intros m q w.
    revert q.
    induction w as [| a w IH]; intros q r; simpl.
    - destruct (fnfa_state_eqb m q r); reflexivity.
    - assert (Hsucc :
        forall idx qs,
          length
            ((fix choices_from_successors
                (idx0 : nat)
                (qs0 : list (nfa_state (fnfa_base m))) : list (list nat) :=
              match qs0 with
              | [] => []
              | q' :: qs' =>
                  map
                    (fun choices => idx0 :: choices)
                    (run_choices_between m q' w r) ++
                  choices_from_successors (S idx0) qs'
              end) idx qs) =
          sum_nats (map (fun q' => runs_between m q' w r) qs)).
      {
        intros idx qs.
        revert idx.
        induction qs as [| q' qs IHqs]; intros idx; simpl.
        - reflexivity.
        - rewrite length_app.
          rewrite map_length.
          rewrite IH.
          rewrite IHqs.
          reflexivity.
      }
      rewrite Hsucc.
      reflexivity.
  Qed.

  Lemma run_choices_between_In_choices :
    forall (m : finite_nfa) q w r choices,
      In choices (run_choices_between m q w r) ->
      run_choices_from (fnfa_base m) q w choices r.
  Proof.
    intros m q w.
    revert q.
    induction w as [| a w IH]; intros q r choices Hin; simpl in Hin.
    - destruct (fnfa_state_eqb m q r) eqn:Heq; simpl in Hin;
        try contradiction.
      destruct Hin as [Hchoices | []].
      subst choices.
      apply fnfa_state_eqb_sound in Heq. subst.
      constructor.
    - assert (Hsucc :
        forall idx qs choices,
          In choices
            ((fix choices_from_successors
                (idx0 : nat)
                (qs0 : list (nfa_state (fnfa_base m))) : list (list nat) :=
              match qs0 with
              | [] => []
              | q' :: qs' =>
                  map
                    (fun choices => idx0 :: choices)
                    (run_choices_between m q' w r) ++
                  choices_from_successors (S idx0) qs'
              end) idx qs) ->
          exists offset q' tail,
            choices = (idx + offset) :: tail /\
            nth_error qs offset = Some q' /\
            run_choices_from (fnfa_base m) q' w tail r).
      {
        intros idx qs.
        revert idx.
        induction qs as [| q' qs IHqs]; intros idx choice Hchoice;
          simpl in Hchoice; try contradiction.
        apply in_app_iff in Hchoice as [Hchoice | Hchoice].
        - apply in_map_iff in Hchoice as [tail [Hchoice_eq Htail]].
          subst choice.
          exists 0, q', tail.
          simpl.
          repeat split.
          + f_equal. lia.
          + now apply IH.
        - destruct (IHqs (S idx) choice Hchoice)
            as [offset [q'' [tail [Hchoice_eq [Hnth Hrun]]]]].
          exists (S offset), q'', tail.
          simpl.
          repeat split; try assumption.
          rewrite Hchoice_eq.
          f_equal. lia.
      }
      destruct (Hsucc 0 (nfa_step (fnfa_base m) q a) choices Hin)
        as [offset [q' [tail [Hchoices [Hnth Hrun]]]]].
      subst choices.
      simpl.
      eapply Run_choices_cons.
      + exact Hnth.
      + exact Hrun.
  Qed.

  Lemma run_choices_between_complete :
    forall (m : finite_nfa) q w r choices,
      run_choices_from (fnfa_base m) q w choices r ->
      In choices (run_choices_between m q w r).
  Proof.
    intros m q w.
    revert q.
    induction w as [| a w IH]; intros q r choices Hrun; simpl.
    - inversion Hrun; subst.
      rewrite fnfa_state_eqb_complete by reflexivity.
      simpl. auto.
    - inversion Hrun as
        [| q0 a0 idx q' w0 tail qf Hnth Htail]; subst.
      assert (Hsucc :
        forall base qs k qnext tail_choice,
          nth_error qs k = Some qnext ->
          In tail_choice (run_choices_between m qnext w r) ->
          In ((base + k) :: tail_choice)
            ((fix choices_from_successors
                (idx0 : nat)
                (qs0 : list (nfa_state (fnfa_base m))) : list (list nat) :=
              match qs0 with
              | [] => []
              | q'' :: qs' =>
                  map
                    (fun choices => idx0 :: choices)
                    (run_choices_between m q'' w r) ++
                  choices_from_successors (S idx0) qs'
              end) base qs)).
      {
        intros base qs.
        revert base.
        induction qs as [| qh qs IHqs]; intros base k qnext tail_choice Hnth2 Hin2;
          destruct k as [| k]; simpl in Hnth2; try discriminate.
        - inversion Hnth2; subst qh.
          simpl.
          apply in_app_iff. left.
          apply in_map_iff.
          exists tail_choice.
          split; [f_equal; lia | exact Hin2].
        - simpl.
          apply in_app_iff. right.
          replace (base + S k) with (S base + k) by lia.
          now apply IHqs with (qnext := qnext).
      }
      replace (idx :: tail) with ((0 + idx) :: tail) by (f_equal; lia).
      eapply Hsucc; eauto.
  Qed.

  Lemma two_distinct_run_choices_between_ge_two :
    forall (m : finite_nfa) q w r c1 c2,
      In c1 (run_choices_between m q w r) ->
      In c2 (run_choices_between m q w r) ->
      c1 <> c2 ->
      2 <= da_from_to m q w r.
  Proof.
    intros m q w r c1 c2 Hc1 Hc2 Hneq.
    unfold da_from_to.
    rewrite <- run_choices_between_length.
    destruct (run_choices_between m q w r) as [| x xs] eqn:Hchoices.
    - contradiction.
    - simpl.
      destruct xs as [| y ys].
      + simpl in Hc1, Hc2.
        destruct Hc1 as [Hc1 | []];
          destruct Hc2 as [Hc2 | []].
        subst. contradiction.
      + simpl. lia.
  Qed.

  Lemma runs_between_app_ge :
    forall (m : finite_nfa) p u q v r,
      runs_between m p u q * runs_between m q v r <=
        runs_between m p (u ++ v) r.
  Proof.
    intros m p u.
    revert p.
    induction u as [| a u IH]; intros p q v r; simpl.
    - destruct (fnfa_state_eqb m p q) eqn:Heq; simpl.
      + apply fnfa_state_eqb_sound in Heq. subst. lia.
      + lia.
    - rewrite <- sum_nats_map_mul_r.
      apply sum_nats_map_ge_pointwise.
      intros p' _.
      apply IH.
  Qed.

  Lemma runs_between_app_ge_two :
    forall (m : finite_nfa) p u q1 q2 v r,
      q1 <> q2 ->
      runs_between m p u q1 * runs_between m q1 v r +
        runs_between m p u q2 * runs_between m q2 v r <=
      runs_between m p (u ++ v) r.
  Proof.
    intros m p u.
    revert p.
    induction u as [| a u IH]; intros p q1 q2 v r Hneq; simpl.
    - destruct (fnfa_state_eqb m p q1) eqn:Hpq1;
        destruct (fnfa_state_eqb m p q2) eqn:Hpq2; simpl.
      + apply fnfa_state_eqb_sound in Hpq1.
        apply fnfa_state_eqb_sound in Hpq2.
        subst. contradiction.
      + apply fnfa_state_eqb_sound in Hpq1. subst. lia.
      + apply fnfa_state_eqb_sound in Hpq2. subst. lia.
      + lia.
    - rewrite <- !sum_nats_map_mul_r.
      rewrite <- sum_nats_map_add.
      apply sum_nats_map_ge_pointwise.
      intros p' _.
      apply IH. exact Hneq.
  Qed.

  Lemma accepting_runs_from_app_ge :
    forall (m : finite_nfa) p u q v,
      runs_between m p u q *
        accepting_runs_from (fnfa_base m) q v <=
      accepting_runs_from (fnfa_base m) p (u ++ v).
  Proof.
    intros m p u.
    revert p.
    induction u as [| a u IH]; intros p q v; simpl.
    - destruct (fnfa_state_eqb m p q) eqn:Heq; simpl.
      + apply fnfa_state_eqb_sound in Heq. subst. lia.
      + lia.
    - rewrite <- sum_nats_map_mul_r.
      apply sum_nats_map_ge_pointwise.
      intros p' _.
      apply IH.
  Qed.

  Lemma ambiguity_of_word_start_ge :
    forall (m : nfa) q0 w,
      In q0 (nfa_start m) ->
      accepting_runs_from m q0 w <= ambiguity_of_word m w.
  Proof.
    intros m q0 w Hstart.
    unfold ambiguity_of_word.
    eapply (@sum_nats_map_In_ge
      (nfa_state m)
      (fun q => accepting_runs_from m q w)); eauto.
  Qed.

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

  Lemma path_runs_between_positive :
    forall (m : finite_nfa) q w r,
      path_from (fnfa_base m) q w r ->
      0 < runs_between m q w r.
  Proof.
    intros m q w r Hpath.
    induction Hpath.
    - simpl.
      rewrite (fnfa_state_eqb_complete m q q eq_refl). lia.
    - simpl.
      eapply sum_nats_map_In_pos; eauto.
  Qed.

  Lemma run_choices_between_exists_from_path :
    forall (m : finite_nfa) q w r,
      path_from (fnfa_base m) q w r ->
      exists choices, In choices (run_choices_between m q w r).
  Proof.
    intros m q w r Hpath.
    pose proof (path_runs_between_positive m q w r Hpath) as Hpos.
    rewrite <- run_choices_between_length in Hpos.
    destruct (run_choices_between m q w r) as [| choices choices'].
    - simpl in Hpos. lia.
    - exists choices. simpl. auto.
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

  Lemma path_accepting_runs_from_positive :
    forall (m : nfa) q w qf,
      path_from m q w qf ->
      nfa_final m qf = true ->
      0 < accepting_runs_from m q w.
  Proof.
    intros m q w qf Hpath Hfinal.
    induction Hpath.
    - simpl. rewrite Hfinal. lia.
    - simpl. eapply sum_nats_map_In_pos; eauto.
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

  Lemma useful_state_from_accepting_trace_nth :
    forall (m : nfa) q0 w qf trace pos mid,
      In q0 (nfa_start m) ->
      run_trace_from m q0 w qf trace ->
      nfa_final m qf = true ->
      nth_error trace pos = Some mid ->
      useful_state m mid.
  Proof.
    intros m q0 w qf trace pos mid Hstart Htrace Hfinal Hnth.
    destruct
      (run_trace_from_nth_prefix_path
        m q0 w qf trace pos mid Htrace Hnth)
      as [w_in Hpath_in].
    destruct
      (run_trace_from_nth_suffix_path
        m q0 w qf trace pos mid Htrace Hnth)
      as [w_out Hpath_out].
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
