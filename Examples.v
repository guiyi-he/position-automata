From Stdlib Require Import List Bool Arith Lia.
Import ListNotations.

From PositionAutomata Require Import
  Sets Syntax PositionAutomaton Equivalence KleeneSemantics PositionCorrectness
  DegreeofAmbiguity DegreeofInfiniteAmbiguity.

Definition a_then_b : regex bool :=
  Cat (Atom true) (Atom false).

Example label_a_then_b :
  label a_then_b = PCat (PAtom 0 true) (PAtom 1 false).
Proof. reflexivity. Qed.

Definition positioned_a_then_b : positioned_regex bool :=
  label a_then_b.

Example nullable_a_then_b :
  nullable positioned_a_then_b = false.
Proof. reflexivity. Qed.

Example firstpos_a_then_b :
  firstpos positioned_a_then_b = [0].
Proof. reflexivity. Qed.

Example lastpos_a_then_b :
  lastpos positioned_a_then_b = [1].
Proof. reflexivity. Qed.

Example followpos_a_then_b :
  followpos positioned_a_then_b = [(0, [1])].
Proof. reflexivity. Qed.

Definition label_of_a_then_b (p : nat) : option bool :=
  match p with
  | 0 => Some true
  | 1 => Some false
  | _ => None
  end.

Definition bool_position_automaton :=
  build Bool.eqb label_of_a_then_b positioned_a_then_b.

Fixpoint nat_list_eqb (xs ys : list nat) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => Nat.eqb x y && nat_list_eqb xs' ys'
  | _, _ => false
  end.

Lemma nat_list_eqb_sound :
  forall xs ys, nat_list_eqb xs ys = true -> xs = ys.
Proof.
  induction xs as [| x xs IH]; destruct ys as [| y ys]; simpl; intros H;
    try discriminate; auto.
  apply andb_true_iff in H as [Hxy Htail].
  apply Nat.eqb_eq in Hxy.
  apply IH in Htail.
  subst. reflexivity.
Qed.

Lemma bool_eqb_sound :
  forall x y, Bool.eqb x y = true -> x = y.
Proof.
  intros [] []; simpl; intros H; try discriminate; reflexivity.
Qed.

Example a_then_b_self_equivb :
  equivb_with_fuel
    [true; false]
    bool_position_automaton
    bool_position_automaton
    nat_list_eqb
    nat_list_eqb
    10 = true.
Proof. reflexivity. Qed.

Example matches_a_then_b :
  matches a_then_b [true; false].
Proof.
  replace [true; false] with ([true] ++ [false]) by reflexivity.
  apply M_Cat.
  - apply M_Atom.
  - apply M_Atom.
Qed.

Example label_semantics_a_then_b :
  exists mw,
    symbols mw = [true; false] /\
    matches_marked (label a_then_b) mw.
Proof.
  apply label_semantics_preserved.
  apply matches_a_then_b.
Qed.

Example accepts_marked_a_then_b :
  accepts_marked positioned_a_then_b [(0, true); (1, false)].
Proof.
  unfold accepts_marked, positioned_a_then_b, a_then_b.
  simpl. repeat split; reflexivity.
Qed.

Example accepts_marked_a_then_b_matches_marked_by_theorem :
  matches_marked positioned_a_then_b [(0, true); (1, false)].
Proof.
  change positioned_a_then_b with (label a_then_b).
  apply accepts_marked_label_matches_marked.
  apply accepts_marked_a_then_b.
Qed.

Example matches_marked_a_then_b_accepts_marked_by_theorem :
  accepts_marked positioned_a_then_b [(0, true); (1, false)].
Proof.
  apply matches_marked_label_accepts_marked.
  unfold a_then_b, label. simpl.
  replace [(0, true); (1, false)] with ([(0, true)] ++ [(1, false)])
    by reflexivity.
  apply MM_Cat; constructor.
Qed.

Example matches_marked_a_then_b_boundary :
  mem 0 (firstpos positioned_a_then_b) = true /\
  label_of positioned_a_then_b 0 = Some true /\
  mem (last_position_from 0 [(1, false)]) (lastpos positioned_a_then_b) = true.
Proof.
  pose proof
    (matches_marked_accepts_marked_boundary
       positioned_a_then_b
       [(0, true); (1, false)]
       (label_positions_nodup a_then_b)) as Hboundary.
  apply Hboundary.
  unfold positioned_a_then_b, a_then_b, label. simpl.
  replace [(0, true); (1, false)] with ([(0, true)] ++ [(1, false)])
    by reflexivity.
  apply MM_Cat; constructor.
Qed.

Example accepts_marked_a_then_b_position_nfa_path :
  accepting_path
    (position_nfa Bool.eqb positioned_a_then_b)
    [true; false].
Proof.
  change [true; false] with (symbols [(0, true); (1, false)]).
  apply accepts_marked_position_nfa_accepting_path.
  - intros [] ; reflexivity.
  - apply accepts_marked_a_then_b.
Qed.

Example position_nfa_path_a_then_b_accepts_marked :
  exists mw,
    symbols mw = [true; false] /\
    accepts_marked positioned_a_then_b mw.
Proof.
  apply position_nfa_accepting_path_accepts_marked with (label_matches := Bool.eqb).
  - intros [] [] H; simpl in H; try discriminate; reflexivity.
  - apply accepts_marked_a_then_b_position_nfa_path.
Qed.

Example matches_a_then_b_position_nfa_path :
  exists mw,
    symbols mw = [true; false] /\
    accepting_path
      (position_nfa Bool.eqb positioned_a_then_b)
      [true; false].
Proof.
  apply regex_match_position_nfa_accepting_path.
  - intros [] ; reflexivity.
  - apply matches_a_then_b.
Qed.

Example position_nfa_a_then_b_one_run :
  ambiguity_of_word
    (position_nfa Bool.eqb positioned_a_then_b)
    [true; false] = 1.
Proof. reflexivity. Qed.

Example position_nfa_a_then_b_no_eda_fuel_2 :
  edab_with_fuel
    2
    (finite_position_nfa [true; false] Bool.eqb positioned_a_then_b) = false.
Proof. reflexivity. Qed.

Definition ambiguous_a : regex bool :=
  Alt (Atom true) (Atom true).

Example accepts_marked_atom_true_matches_marked :
  matches_marked (PAtom 0 true) [(0, true)].
Proof.
  apply accepts_marked_atom_matches_marked.
  simpl. repeat split; reflexivity.
Qed.

Example accepts_marked_alt_true_matches_marked :
  matches_marked (label ambiguous_a) [(0, true)].
Proof.
  change (label ambiguous_a) with (PAlt (PAtom 0 true) (PAtom 1 true)).
  eapply accepts_marked_alt_matches_marked.
  - simpl. repeat constructor; simpl; lia.
  - intros mw Hacc. apply accepts_marked_atom_matches_marked. exact Hacc.
  - intros mw Hacc. apply accepts_marked_atom_matches_marked. exact Hacc.
  - simpl. repeat split; reflexivity.
Qed.

Example position_nfa_ambiguous_a_two_runs :
  ambiguity_of_word
    (position_nfa Bool.eqb (label ambiguous_a))
    [true] = 2.
Proof. reflexivity. Qed.

Example position_nfa_ambiguous_a_accepting_endpoints :
  accepting_run_endpoints
    (finite_position_nfa [true; false] Bool.eqb (label ambiguous_a))
    [true] = [Some 0; Some 1].
Proof. reflexivity. Qed.

Example position_nfa_ambiguous_a_accepting_endpoints_length :
  length
    (accepting_run_endpoints
      (finite_position_nfa [true; false] Bool.eqb (label ambiguous_a))
      [true]) =
    ambiguity_of_word
      (position_nfa Bool.eqb (label ambiguous_a))
      [true].
Proof.
  apply accepting_run_endpoints_length.
Qed.

Definition unit_eqb (_ _ : unit) : bool := true.

Lemma unit_eqb_sound :
  forall x y, unit_eqb x y = true -> x = y.
Proof.
  intros [] [] _. reflexivity.
Qed.

Lemma unit_eqb_complete :
  forall x y, x = y -> unit_eqb x y = true.
Proof.
  intros [] [] _. reflexivity.
Qed.

Definition duplicated_loop_nfa : @finite_nfa bool :=
  {|
    fnfa_base :=
      {|
        nfa_state := unit;
        nfa_start := [tt];
        nfa_final := fun _ => true;
        nfa_step := fun (_ : unit) (a : bool) => if a then [tt; tt] else []
      |};
    fnfa_states := [tt];
    fnfa_alphabet := [true];
    fnfa_state_eqb := unit_eqb;
    fnfa_state_eqb_sound := unit_eqb_sound;
    fnfa_state_eqb_complete := unit_eqb_complete
  |}.

Example duplicated_loop_word_has_two_runs :
  ambiguity_of_word duplicated_loop_nfa [true] = 2.
Proof. reflexivity. Qed.

Example duplicated_loop_choices_one_symbol :
  accepting_run_choices duplicated_loop_nfa [true] = [[0]; [1]].
Proof. reflexivity. Qed.

Example duplicated_loop_full_choices_one_symbol :
  accepting_run_full_choices duplicated_loop_nfa [true] = [[0; 0]; [0; 1]].
Proof. reflexivity. Qed.

Example duplicated_loop_choices_length_matches_ambiguity :
  length (accepting_run_choices duplicated_loop_nfa [true]) =
    ambiguity_of_word duplicated_loop_nfa [true].
Proof.
  apply accepting_run_choices_length.
Qed.

Example duplicated_loop_full_choices_length_matches_ambiguity :
  length (accepting_run_full_choices duplicated_loop_nfa [true]) =
    ambiguity_of_word duplicated_loop_nfa [true].
Proof.
  apply accepting_run_full_choices_length.
Qed.

Example duplicated_loop_edab :
  edab_with_fuel 1 duplicated_loop_nfa = true.
Proof. reflexivity. Qed.

Example duplicated_loop_eda :
  EDA duplicated_loop_nfa.
Proof.
  apply edab_with_fuel_sound with (fuel := 1).
  reflexivity.
Qed.

Example duplicated_loop_exponentially_ambiguous :
  exponentially_ambiguous duplicated_loop_nfa.
Proof.
  apply edab_with_fuel_exponentially_ambiguous with (fuel := 1).
  reflexivity.
Qed.

Example duplicated_loop_growth_result :
  ambiguity_growth_lower_bound_with_fuel 1 duplicated_loop_nfa 3 =
    GrowthExponential.
Proof. reflexivity. Qed.

Example duplicated_loop_g5_candidate :
  ambiguity_growth_g5_candidate_with_fuel 1 1 duplicated_loop_nfa =
    GrowthExponential.
Proof. reflexivity. Qed.

Example duplicated_loop_g5_lower_bound :
  ambiguity_growth_g5_lower_bound_with_fuel 1 1 duplicated_loop_nfa =
    GrowthExponential.
Proof. reflexivity. Qed.

Example duplicated_loop_g5_lower_bound_sound :
  exponentially_ambiguous duplicated_loop_nfa.
Proof.
  apply ambiguity_growth_g5_lower_bound_with_fuel_sound_exponential
    with (word_fuel := 1) (graph_fuel := 1).
  reflexivity.
Qed.

Definition single_loop_nfa : @finite_nfa bool :=
  {|
    fnfa_base :=
      {|
        nfa_state := unit;
        nfa_start := [tt];
        nfa_final := fun _ => true;
        nfa_step := fun (_ : unit) (a : bool) => if a then [tt] else []
      |};
    fnfa_states := [tt];
    fnfa_alphabet := [true];
    fnfa_state_eqb := unit_eqb;
    fnfa_state_eqb_sound := unit_eqb_sound;
    fnfa_state_eqb_complete := unit_eqb_complete
  |}.

Lemma single_loop_runs_between_le_one :
  forall w, da_from_to single_loop_nfa tt w tt <= 1.
Proof.
  induction w as [| a w IH]; simpl.
  - lia.
  - destruct a; simpl; lia.
Qed.

Example single_loop_no_eda :
  no_EDA single_loop_nfa.
Proof.
  intros [q [v [_ [_ Hcount]]]].
  destruct q.
  pose proof (single_loop_runs_between_le_one v).
  lia.
Qed.

Example single_loop_g5_lower_bound :
  ambiguity_growth_g5_lower_bound_with_fuel 1 1 single_loop_nfa =
    GrowthPolynomialLowerBound 0.
Proof. reflexivity. Qed.

Example single_loop_no_eda_g5_polynomial_branch :
  ambiguity_growth_g5_lower_bound_with_fuel 1 1 single_loop_nfa =
    GrowthPolynomialLowerBound
      (max_g5_red_depth_with_fuel
         1
         1
         single_loop_nfa
         (length (scc_quotient_with_fuel 1 single_loop_nfa))).
Proof.
  apply no_EDA_ambiguity_growth_g5_lower_bound_polynomial_branch.
  apply single_loop_no_eda.
Qed.

Lemma single_loop_accepting_runs_from_le_one :
  forall w,
    word_in_alphabet single_loop_nfa w ->
    accepting_runs_from single_loop_nfa tt w <= 1.
Proof.
  intros w Hall.
  induction Hall as [| a w Ha Hall IH]; simpl.
  - lia.
  - destruct a; simpl in *.
    + lia.
    + destruct Ha as [Ha | []]. discriminate.
Qed.

Example single_loop_choices_two_symbols :
  accepting_run_choices single_loop_nfa [true; true] = [[0; 0]].
Proof. reflexivity. Qed.

Example single_loop_full_choices_two_symbols :
  accepting_run_full_choices single_loop_nfa [true; true] = [[0; 0; 0]].
Proof. reflexivity. Qed.

Example single_loop_degree_at_most_0 :
  degree_at_most_on_alphabet single_loop_nfa 0.
Proof.
  apply degree_at_most_on_alphabet_from_start_state_bounds
    with (d := 0) (c := 1).
  intros [] _ w Hall.
  simpl.
  pose proof (single_loop_accepting_runs_from_le_one w Hall).
  change (accepting_runs_from single_loop_nfa tt w <= 1).
  assumption.
Qed.

Example single_loop_occurrence_codes_upper_0 :
  accepting_endpoint_occurrence_codes_upper_on_alphabet
    single_loop_nfa unit 0 1.
Proof.
  intros w Hall.
  exists [tt].
  split.
  - constructor.
    + intros [].
    + constructor.
  - split.
    + simpl. lia.
    + exists (fun _ => tt).
      split.
      * intros i _Hi. simpl. auto.
      * intros i j Hi Hj _Heq.
        assert (Hlen :
          length (accepting_run_endpoints single_loop_nfa w) <= 1).
        {
          rewrite accepting_run_endpoints_length.
          unfold ambiguity_of_word. simpl.
          change (accepting_runs_from single_loop_nfa tt w + 0 <= 1).
          pose proof (single_loop_accepting_runs_from_le_one w Hall).
          lia.
        }
        lia.
Qed.

Example single_loop_degree_at_most_0_from_occurrence_codes :
  degree_at_most_on_alphabet single_loop_nfa 0.
Proof.
  eapply degree_at_most_on_alphabet_from_occurrence_codes
    with (Code := unit) (c := 1).
  apply single_loop_occurrence_codes_upper_0.
Qed.

Example single_loop_polynomial_signatures_0 :
  accepting_endpoint_polynomial_signatures_on_alphabet
    single_loop_nfa unit [tt] 0 1.
Proof.
  split.
  - constructor.
    + intros [].
    + constructor.
  - split.
    + simpl. lia.
    + intros w Hall.
      exists (fun _ => ([], tt)).
      split.
      * intros i _Hi. simpl. auto.
      * intros i j Hi Hj _Heq.
        assert (Hlen :
          length (accepting_run_endpoints single_loop_nfa w) <= 1).
        {
          rewrite accepting_run_endpoints_length.
          unfold ambiguity_of_word. simpl.
          change (accepting_runs_from single_loop_nfa tt w + 0 <= 1).
          pose proof (single_loop_accepting_runs_from_le_one w Hall).
          lia.
        }
        lia.
Qed.

Example single_loop_degree_at_most_0_from_polynomial_signatures :
  degree_at_most_on_alphabet single_loop_nfa 0.
Proof.
  eapply degree_at_most_on_alphabet_from_polynomial_signatures
    with (Payload := unit) (payloads := [tt]) (c := 1).
  apply single_loop_polynomial_signatures_0.
Qed.

Example single_loop_g5_walk_signatures_0 :
  accepting_endpoint_g5_walk_signatures_on_alphabet
    1 single_loop_nfa unit [tt] 0 1.
Proof.
  split.
  - constructor.
    + intros [].
    + constructor.
  - split.
    + simpl. lia.
    + intros w Hall.
      exists (fun _ => [[tt]]).
      exists (fun _ => tt).
      split.
      * intros i _Hi. repeat split; simpl; auto; lia.
      * intros i j Hi Hj _Heq.
        assert (Hlen :
          length (accepting_run_endpoints single_loop_nfa w) <= 1).
        {
          rewrite accepting_run_endpoints_length.
          unfold ambiguity_of_word. simpl.
          change (accepting_runs_from single_loop_nfa tt w + 0 <= 1).
          pose proof (single_loop_accepting_runs_from_le_one w Hall).
          lia.
        }
        lia.
Qed.

Example single_loop_degree_at_most_0_from_g5_walk_signatures :
  degree_at_most_on_alphabet single_loop_nfa 0.
Proof.
  eapply degree_at_most_on_alphabet_from_g5_walk_signatures
    with (word_fuel := 1) (Payload := unit) (payloads := [tt]) (c := 1).
  apply single_loop_g5_walk_signatures_0.
Qed.

Example single_loop_run_g5_walk_signatures_0 :
  accepting_run_g5_walk_signatures_on_alphabet
    1 single_loop_nfa unit [tt] 0 1.
Proof.
  split.
  - constructor.
    + intros [].
    + constructor.
  - split.
    + simpl. lia.
    + intros w Hall.
      exists (fun _ => [[tt]]).
      exists (fun _ => tt).
      split.
      * intros i _Hi. repeat split; simpl; auto; lia.
      * intros i j Hi Hj _Heq.
        assert (Hlen :
          length (accepting_run_full_choices single_loop_nfa w) <= 1).
        {
          rewrite accepting_run_full_choices_length.
          unfold ambiguity_of_word. simpl.
          change (accepting_runs_from single_loop_nfa tt w + 0 <= 1).
          pose proof (single_loop_accepting_runs_from_le_one w Hall).
          lia.
        }
        lia.
Qed.

Example single_loop_degree_at_most_0_from_run_g5_walk_signatures :
  degree_at_most_on_alphabet single_loop_nfa 0.
Proof.
  eapply degree_at_most_on_alphabet_from_run_g5_walk_signatures
    with (word_fuel := 1) (Payload := unit) (payloads := [tt]) (c := 1).
  apply single_loop_run_g5_walk_signatures_0.
Qed.

Example single_loop_degree_at_least_0 :
  degree_at_least single_loop_nfa 0.
Proof.
  intros n.
  exists [].
  change (Nat.pow n 0 <= 1).
  destruct n; reflexivity.
Qed.

Example single_loop_exact_degree_0 :
  exact_polynomial_degree_on_alphabet single_loop_nfa 0.
Proof.
  split.
  - apply single_loop_degree_at_least_0.
  - apply single_loop_degree_at_most_0.
Qed.

Definition nat_state_step (q : nat) (a : bool) : list nat :=
  if a then
    match q with
    | 0 => [0; 1]
    | 1 => [1]
    | _ => []
    end
  else [].

Lemma nat_eqb_complete :
  forall x y : nat, x = y -> Nat.eqb x y = true.
Proof.
  intros x y H. subst. apply Nat.eqb_refl.
Qed.

Lemma nat_eqb_sound :
  forall x y : nat, Nat.eqb x y = true -> x = y.
Proof.
  intros x y H. now apply Nat.eqb_eq.
Qed.

Definition ida_example_nfa : @finite_nfa bool :=
  {|
    fnfa_base :=
      {|
        nfa_state := nat;
        nfa_start := [0];
        nfa_final := fun q => Nat.leb q 1;
        nfa_step := nat_state_step
      |};
    fnfa_states := [0; 1];
    fnfa_alphabet := [true];
    fnfa_state_eqb := Nat.eqb;
    fnfa_state_eqb_sound := nat_eqb_sound;
    fnfa_state_eqb_complete := nat_eqb_complete
  |}.

Example ida_example_idab :
  idab_with_fuel 1 ida_example_nfa = true.
Proof. reflexivity. Qed.

Example ida_example_idab_d_1 :
  idab_d_with_fuel 1 ida_example_nfa 1 = true.
Proof. reflexivity. Qed.

Example ida_example_satisfies_ida :
  IDA ida_example_nfa.
Proof.
  apply idab_with_fuel_sound with (fuel := 1).
  reflexivity.
Qed.

Example ida_example_satisfies_ida_d_1 :
  IDA_d ida_example_nfa 1.
Proof.
  apply idab_with_fuel_sound_IDA_d_1 with (fuel := 1).
  reflexivity.
Qed.

Example ida_example_degree_at_least_1 :
  degree_at_least (fnfa_base ida_example_nfa) 1.
Proof.
  apply idab_d_with_fuel_degree_at_least with (fuel := 1).
  reflexivity.
Qed.

Example ida_example_g5_max_red_path :
  g5_max_red_path_with_fuel 1 1 ida_example_nfa = 1.
Proof. reflexivity. Qed.

Example ida_example_g5_red_pathb_1 :
  g5_red_pathb_with_fuel 1 1 ida_example_nfa 1 = true.
Proof. reflexivity. Qed.

Example ida_example_max_g5_red_depth :
  max_g5_red_depth_with_fuel 1 1 ida_example_nfa 2 = 1.
Proof. reflexivity. Qed.

Example ida_example_g5_candidate :
  ambiguity_growth_g5_candidate_with_fuel 1 1 ida_example_nfa =
    GrowthPolynomialLowerBound 1.
Proof. reflexivity. Qed.

Example ida_example_g5_lower_bound :
  ambiguity_growth_g5_lower_bound_with_fuel 1 1 ida_example_nfa =
    GrowthPolynomialLowerBound 1.
Proof. reflexivity. Qed.

Example ida_example_g5_lower_bound_sound :
  degree_at_least (fnfa_base ida_example_nfa) 1.
Proof.
  apply ambiguity_growth_g5_lower_bound_with_fuel_sound_polynomial
    with (word_fuel := 1) (graph_fuel := 1).
  reflexivity.
Qed.

Definition chain2_step (q : nat) (a : bool) : list nat :=
  if a then
    match q with
    | 0 => [0; 1]
    | 1 => [1]
    | 2 => [2; 3]
    | 3 => [3]
    | _ => []
    end
  else
    match q with
    | 1 => [2]
    | _ => []
    end.

Definition ida_chain2_nfa : @finite_nfa bool :=
  {|
    fnfa_base :=
      {|
        nfa_state := nat;
        nfa_start := [0; 1; 2; 3];
        nfa_final := fun q => Nat.leb q 3;
        nfa_step := chain2_step
      |};
    fnfa_states := [0; 1; 2; 3];
    fnfa_alphabet := [true; false];
    fnfa_state_eqb := Nat.eqb;
    fnfa_state_eqb_sound := nat_eqb_sound;
    fnfa_state_eqb_complete := nat_eqb_complete
  |}.

Example ida_chain2_idab_d_2 :
  idab_d_with_fuel 1 ida_chain2_nfa 2 = true.
Proof. reflexivity. Qed.

Example ida_chain2_degree_at_least_2 :
  degree_at_least (fnfa_base ida_chain2_nfa) 2.
Proof.
  apply idab_d_with_fuel_degree_at_least with (fuel := 1).
  reflexivity.
Qed.

Example ida_chain2_growth_result :
  ambiguity_growth_lower_bound_with_fuel 1 ida_chain2_nfa 3 =
    GrowthPolynomialLowerBound 2.
Proof. reflexivity. Qed.

Example ida_chain2_growth_result_sound :
  degree_at_least (fnfa_base ida_chain2_nfa) 2.
Proof.
  apply ambiguity_growth_lower_bound_with_fuel_sound_polynomial
    with (fuel := 1) (max_d := 3).
  reflexivity.
Qed.

Example ida_chain2_graph_idab_d_2 :
  idab_d_graph_with_fuel 1 1 ida_chain2_nfa 2 = true.
Proof. reflexivity. Qed.

Example ida_chain2_graph_growth_result :
  ambiguity_growth_lower_bound_graph_with_fuel 1 1 ida_chain2_nfa 3 =
    GrowthPolynomialLowerBound 2.
Proof. reflexivity. Qed.

Example ida_chain2_graph_growth_result_sound :
  degree_at_least (fnfa_base ida_chain2_nfa) 2.
Proof.
  apply ambiguity_growth_lower_bound_graph_with_fuel_sound_polynomial
    with (word_fuel := 1) (graph_fuel := 1) (max_d := 3).
  reflexivity.
Qed.

Example ida_chain2_scc_quotient :
  scc_quotient_with_fuel 1 ida_chain2_nfa = [[0]; [1]; [2]; [3]].
Proof. reflexivity. Qed.

Definition ida_chain2_components : list (quotient_component ida_chain2_nfa) :=
  scc_quotient_with_fuel 1 ida_chain2_nfa.

Example ida_chain2_g5_walkb_full :
  g5_walkb 1 1 ida_chain2_nfa ida_chain2_components = true.
Proof. reflexivity. Qed.

Example ida_chain2_g5_walk_red_edges :
  g5_red_edges_on_walk 1 ida_chain2_nfa ida_chain2_components = 2.
Proof. reflexivity. Qed.

Example ida_chain2_g5_no_red_self_loop :
  g5_has_red_self_loopb 1 1 ida_chain2_nfa = false.
Proof. reflexivity. Qed.

Example ida_chain2_g5_max_red_path :
  g5_max_red_path_with_fuel 1 1 ida_chain2_nfa = 2.
Proof. reflexivity. Qed.

Example ida_chain2_g5_red_pathb_2 :
  g5_red_pathb_with_fuel 1 1 ida_chain2_nfa 2 = true.
Proof. reflexivity. Qed.

Example ida_chain2_max_g5_red_depth :
  max_g5_red_depth_with_fuel 1 1 ida_chain2_nfa 4 = 2.
Proof. reflexivity. Qed.

Example ida_chain2_g5_candidate :
  ambiguity_growth_g5_candidate_with_fuel 1 1 ida_chain2_nfa =
    GrowthPolynomialLowerBound 2.
Proof. reflexivity. Qed.

Example ida_chain2_g5_lower_bound :
  ambiguity_growth_g5_lower_bound_with_fuel 1 1 ida_chain2_nfa =
    GrowthPolynomialLowerBound 2.
Proof. reflexivity. Qed.

Example ida_chain2_g5_lower_bound_sound :
  degree_at_least (fnfa_base ida_chain2_nfa) 2.
Proof.
  apply ambiguity_growth_g5_lower_bound_with_fuel_sound_polynomial
    with (word_fuel := 1) (graph_fuel := 1).
  reflexivity.
Qed.
