Require Import List.
Import ListNotations.

From PositionAutomata Require Import Sets Syntax.

Section PositionAutomaton.
  Context {A : Type}.

  Definition symbol_at := nat -> option A.

  Fixpoint atoms (r : positioned_regex A) : list (nat * A) :=
    match r with
    | PEmpty | PEps => []
    | PAtom p a => [(p, a)]
    | PAlt r1 r2 | PCat r1 r2 => atoms r1 ++ atoms r2
    | PStar r' => atoms r'
    end.

  Fixpoint lookup_symbol (p : nat) (ats : list (nat * A)) : option A :=
    match ats with
    | [] => None
    | (q, a) :: ats' => if Nat.eqb p q then Some a else lookup_symbol p ats'
    end.

  Definition label_of (r : positioned_regex A) : symbol_at :=
    fun p => lookup_symbol p (atoms r).

  Fixpoint nullable (r : positioned_regex A) : bool :=
    match r with
    | PEmpty => false
    | PEps => true
    | PAtom _ _ => false
    | PAlt r1 r2 => nullable r1 || nullable r2
    | PCat r1 r2 => nullable r1 && nullable r2
    | PStar _ => true
    end.

  Fixpoint firstpos (r : positioned_regex A) : set :=
    match r with
    | PEmpty | PEps => []
    | PAtom p _ => [p]
    | PAlt r1 r2 => union (firstpos r1) (firstpos r2)
    | PCat r1 r2 =>
        if nullable r1
        then union (firstpos r1) (firstpos r2)
        else firstpos r1
    | PStar r' => firstpos r'
    end.

  Fixpoint lastpos (r : positioned_regex A) : set :=
    match r with
    | PEmpty | PEps => []
    | PAtom p _ => [p]
    | PAlt r1 r2 => union (lastpos r1) (lastpos r2)
    | PCat r1 r2 =>
        if nullable r2
        then union (lastpos r1) (lastpos r2)
        else lastpos r2
    | PStar r' => lastpos r'
    end.
(* a1*b2* {{1,xx}, {2,xx}} *)
  Definition follow_table := list (nat * set).

  Fixpoint lookup_follow (p : nat) (t : follow_table) : set :=
    match t with
    | [] => []
    | (q, ps) :: t' => if Nat.eqb p q then ps else lookup_follow p t'
    end.

  Fixpoint add_follow (p : nat) (ps : set) (t : follow_table) : follow_table :=
    match t with
    | [] => [(p, ps)]
    | (q, qs) :: t' =>
        if Nat.eqb p q
        then (q, union ps qs) :: t'
        else (q, qs) :: add_follow p ps t'
    end.

  Fixpoint add_follow_all (from to_ : set) (t : follow_table) : follow_table :=
    match from with
    | [] => t
    | p :: from' => add_follow_all from' to_ (add_follow p to_ t)
    end.

  Fixpoint followpos (r : positioned_regex A) : follow_table :=
    match r with
    | PEmpty | PEps | PAtom _ _ => []
    | PAlt r1 r2 => followpos r1 ++ followpos r2
    | PCat r1 r2 =>
        add_follow_all (lastpos r1) (firstpos r2) (followpos r1 ++ followpos r2)
    | PStar r' =>
        add_follow_all (lastpos r') (firstpos r') (followpos r')
    end.

  Record automaton : Type := {
    state : Type;
    start : state;
    final : state -> bool;
    step : state -> A -> state
  }.

  Definition pa_state := set.
  Definition standard_pa_state := option nat.

  Definition is_final (r : positioned_regex A) (s : pa_state) : bool :=
    subset (lastpos r) s.

  Definition transition_with
      (label_matches : A -> A -> bool)
      (label_of : symbol_at)
      (tbl : follow_table)
      (s : pa_state)
      (a : A) : pa_state :=
    fold_right
      (fun p acc =>
         match label_of p with
         | Some b =>
             if label_matches b a
             then union (lookup_follow p tbl) acc
             else acc
         | None => acc
         end)
      []
      s.

  Definition build
      (label_matches : A -> A -> bool)
      (label_of : symbol_at)
      (r : positioned_regex A) : automaton :=
    let tbl := followpos r in
    {|
      state := pa_state;
      start := firstpos r;
      final := is_final r;
      step := transition_with label_matches label_of tbl
    |}.

  Definition build_from_regex
      (label_matches : A -> A -> bool)
      (label_of : symbol_at)
      (r : regex A) : automaton :=
    build label_matches label_of (label r).

  Fixpoint run_from_marked
      (tbl : follow_table)
      (lbl : symbol_at)
      (p : nat)
      (mw : list (nat * A)) : Prop :=
    match mw with
    | [] => True
    | (q, a) :: mw' =>
        mem q (lookup_follow p tbl) = true /\
        lbl q = Some a /\
        run_from_marked tbl lbl q mw'
    end.

  Definition accepts_marked
      (r : positioned_regex A)
      (mw : list (nat * A)) : Prop :=
    let tbl := followpos r in
    let lbl := label_of r in
    match mw with
    | [] => nullable r = true
    | (p, a) :: mw' =>
        mem p (firstpos r) = true /\
        lbl p = Some a /\
        run_from_marked tbl lbl p mw' /\
        match List.rev mw with
        | [] => False
        | (q, _) :: _ => mem q (lastpos r) = true
        end
    end.

  Definition standard_final (r : positioned_regex A) (s : standard_pa_state) : bool :=
    match s with
    | None => nullable r
    | Some p => mem p (lastpos r)
    end.

  Definition standard_step
      (label_matches : A -> A -> bool)
      (lbl : symbol_at)
      (tbl : follow_table)
      (r : positioned_regex A)
      (s : standard_pa_state)
      (a : A) : pa_state :=
    match s with
    | None =>
        fold_right
          (fun p acc =>
             match lbl p with
             | Some b =>
                 if label_matches b a
                 then add p acc
                 else acc
             | None => acc
             end)
          []
          (firstpos r)
    | Some p =>
        fold_right
          (fun q acc =>
             match lbl q with
             | Some b =>
                 if label_matches b a
                 then add q acc
                 else acc
             | None => acc
             end)
          []
          (lookup_follow p tbl)
    end.
End PositionAutomaton.
