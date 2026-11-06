import Mathlib

/- NLD   Five identical empty buckets of 2-liter capacity stand at the vertices of a regular pentagon. Cinderella and her wicked Stepmother go through a sequence of rounds: At the beginning of every round, the Stepmother takes one liter of water from the nearby river and distributes it arbitrarily over the five buckets. Then Cinderella chooses a pair of neighboring buckets, empties them into the river, and puts them back. Then the next round begins. The Stepmother's goal is to make one of these buckets overflow. Cinderella's goal is to prevent this. Can the wicked Stepmother enforce a bucket overflow?
-/

-- Trivial facts about $\mathbb{Z} / 5\mathbb{Z}$
lemma mod_five_exhaust : ∀ i : ZMod 5, ∀ j : ZMod 5, j = i ∨ j = i + 1 ∨ j = i + 2 ∨ j = i + 3 ∨ j = i + 4 := by
  suffices ∀ k : ZMod 5, k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 by
    intro i j
    rcases this (j - i) with (h|h|h|h|h)
    · left
      rwa [← sub_eq_zero]
    · right
      left
      rw [← sub_add_cancel j i, h, add_comm]
    · right
      right
      left
      rw [← sub_add_cancel j i, h, add_comm]
    · right
      right
      right
      left
      rw [← sub_add_cancel j i, h, add_comm]
    · right
      right
      right
      right
      rw [← sub_add_cancel j i, h, add_comm]
  intro k
  fin_cases k <;> simp

lemma mod_five_exhaust' (i : ZMod 5) : (Finset.univ : Finset (ZMod 5)) = {i, i + 1, i + 2, i + 3, i + 4} := by
  ext j
  simp
  apply mod_five_exhaust

lemma sum_mod_five (x : ZMod 5 → NNReal) (i : ZMod 5) : ∑ j, x j = x i + x (i + 1) + x (i + 2) + x (i + 3) + x (i + 4) := by
  rw [mod_five_exhaust' i]
  have s2 : ∑ j ∈ {i + 3, i + 4}, x j = x (i + 3) + x (i + 4) := by
    apply Finset.sum_pair
    simp [add_left_cancel_iff]
    trivial
  have s3 : ∑ j ∈ {i + 2, i + 3, i + 4}, x j = x (i + 2) + x (i + 3) + x (i + 4) := by
    rw [add_assoc, ← s2]
    apply Finset.sum_insert
    simp
    trivial
  have s4 : ∑ j ∈ {i + 1, i + 2, i + 3, i + 4}, x j = x (i + 1) + x (i + 2) + x (i + 3) + x (i + 4) := by
    rw [add_assoc, add_assoc]
    conv in x (i + 2) + _ =>
      rw [← add_assoc]
    rw [← s3]
    apply Finset.sum_insert
    simp
    trivial
  repeat rw [add_assoc]
  conv in x (i + 1) + _ =>
      repeat rw [← add_assoc]
  rw [← s4]
  apply Finset.sum_insert
  simp
  trivial

-- We formalize the setting of the problem.
-- A state of the game is encoded by five nonnegative real numbers indexed by $\mathbb{Z} / 5\mathbb{Z}$, each representing the content of a bucket. Thus, adjacent buckets are indexed by $i$ and $i + 1 mod 5$.
-- Admissible moves of each player are reprensented by a function from the set of the states to a set of sets of states.
-- Cindrella's move is emptying two buckets.
abbrev State := ZMod 5 → NNReal
abbrev Cindrella_move (y : State) : Set State := 
  { x : (ZMod 5) → NNReal | ∃ i : ZMod 5, x i = 0 ∧ x (i+1) = 0 ∧ x (i + 2) = y (i + 2) ∧ x (i + 3) = y (i + 3) ∧ x (i + 4) = y (i + 4)}
-- Stepmother's move increases the total sum by 1.
abbrev Stepmother_move (x : State) : Set State := 
  { y : (ZMod 5) → NNReal | (∀ i : ZMod 5, x i ≤ y i) ∧ ∑ i : ZMod 5, y i = 1 + ∑ i : ZMod 5, x i }

-- We show a useful lemma: after Stepmother's move, the content of a bucket can increase by at most 1
lemma y_le_one_add_x (x : State) (y : State) (hy : y ∈ Stepmother_move x) : ∀ i : ZMod 5, y i ≤ 1 + x i := by
  intro i
  have h0 := hy.2
  rw [sum_mod_five y i, sum_mod_five x i] at h0
  have h1 := hy.1 (i + 1)
  have h2 := hy.1 (i + 2)
  have h3 := hy.1 (i + 3)
  have h4 := hy.1 (i + 4)
  rw [← NNReal.coe_le_coe] at *
  rw [NNReal.eq_iff] at h0
  push_cast at h0 ⊢
  linarith

lemma y_le_one_add_x' (x : State) (y : State) (hy : y ∈ Stepmother_move x) : ∀ i : ZMod 5, y i + y (i + 1) + y (i + 2) + y (i + 4) ≤ 1 + x i + x (i + 1) + x (i + 2) + x (i + 4) := by
  intro i
  have h0 := hy.2
  rw [sum_mod_five y i, sum_mod_five x i]at h0
  have h3 := hy.1 (i + 3)
  rw [← NNReal.coe_le_coe] at *
  rw [NNReal.eq_iff] at h0
  push_cast at h0 ⊢
  linarith


-- Cindrella has a wining strategy if and only if she has a strategy such that no matter what the stepmother's strategy is, stepmother's goal is not achieved.
-- By strategy we mean a function from the set of previous states to a new admissible state.
abbrev Cindrella_strategy := (y : State) → Cindrella_move y
abbrev Stepmother_strategy := (x : State) → Stepmother_move x
abbrev Stepmother_wining_state (y : State) : Prop := ∃ i, y i > 2
-- A game is the sequence of states given both players strategy.
def game (s : Cindrella_strategy) (t : Stepmother_strategy)
  | 0     => fun _ => 0
  | n + 1 => if Even n then (t (game s t n)).val else (s (game s t n)).val
def Cindrella_has_a_wining_strategy := ∃ s : Cindrella_strategy, ∀ t : Stepmother_strategy, ∀ n : ℕ, ¬ Stepmother_wining_state (game s t (2 * n + 1))

theorem combinatorics_23826 : Cindrella_has_a_wining_strategy := by
  -- Cinderella enforces that the following three conditions are satisfied at the beginning of every round: (1) Two adjacent buckets (say $B\_{1}$ and $B\_{2}$ ) are empty. (2) The two buckets standing next to these adjacent buckets (here $B\_{0}$ and $B\_{3}$ ) have total contents at most 1. (3) The remaining bucket (here $B\_{4}$ ) has contents at most 1.
  let Cindrella_condition (x : State) : Prop :=
    ∃ i, x i = 0 ∧ x (i + 1) = 0 ∧ x (i + 2) + x (i + 4) ≤ 1 ∧ x (i + 3) ≤ 1

  -- Denote by $x_{k}(k=0,1,2,3,4)$ the contents of bucket $B_{k}$ at the beginning of this round and by $y_{k}$ the corresponding contents after the Stepmother has distributed her liter of water in this round. 
  -- By the conditions, we can assume $x_{1}=x_{2}=0, x_{0}+x_{3} \leq 1$ and $x_{4} \leq 1$. Then, since the Stepmother adds one liter, we conclude $y_{0}+y_{1}+y_{2}+y_{3} \leq 2$. This inequality implies $y_{0}+y_{2} \leq 1$ or $y_{1}+y_{3} \leq 1$.
  -- For reasons of symmetry, we only consider the second case. Then Cinderella empties buckets $B_{0}$ and $B_{4}$. At the beginning of the next round $B_{0}$ and $B_{4}$ are empty (condition (1) is fulfilled), due to $y_{1}+y_{3} \leq 1$ condition (2) is fulfilled and finally since $x_{2}=0$ we also must have $y_{2} \leq 1$ (condition (3) is fulfilled). Therefore, Cinderella can indeed manage to maintain the three conditions (1)-(3) also at the beginning of the next round. 
  have key (x : State) (hx : Cindrella_condition x) (y : State) (hy : y ∈ Stepmother_move x) : ∃ x' : State, x' ∈ Cindrella_move y ∧ Cindrella_condition x' := by
    obtain ⟨i,hi⟩ := hx
    have hs : x i + x (i + 1) + x (i + 2) + x (i + 4) ≤ 1 := by
      simp [hi.1, hi.2.1]
      exact hi.2.2.1
    replace hs : y i + y (i + 1) + y (i + 2) + y (i + 4) ≤ 2 := by
      have := y_le_one_add_x' x y hy i
      rw [← NNReal.coe_le_coe] at this hs ⊢
      push_cast at this hs ⊢
      linarith
    by_cases h : y i + y (i + 2) ≤ 1
    · use fun j => if j = i + 3 ∨ j = i + 4 then 0 else y j
      constructor
      · use (i + 3)
        simp!
        group
        simp
      · use (i + 3)
        simp
        group
        simp
        constructor
        · rw [ite_cond_eq_false]
          rw [ite_cond_eq_false]
          convert h using 3
          apply zero_add
          group
          congr 1
          trivial
          trivial
        · rw [ite_cond_eq_false]
          · suffices y (i + 1) ≤ 1 + x (i + 1) by
              have h6 : 6 + i = i + 1 := by
                group
                congr 1
              rw [h6]
              simp [hi.2.1] at this
              exact this
            apply y_le_one_add_x
            assumption
          · simp
            push_neg
            trivial
    · push_neg at h
      replace h : y (i + 1) + y (i + 4) ≤ 1 := by
          by_contra! h1
          absurd hs
          push_neg
          rw [(by norm_num : (2 : NNReal) = 1 + 1), (by ring : y i + y (i + 1) + y (i + 2) + y (i + 4) = (y i + y (i + 2)) + (y (i + 1) + y (i + 4)))]
          apply add_lt_add
          exact h
          exact h1
      use fun j => if j = i + 2 ∨ j = i + 3 then 0 else y j
      constructor
      · use (i + 2)
        simp!
        group
        simp
      · use (i + 2)
        simp
        group
        simp
        constructor
        · rw [ite_cond_eq_false]
          rw [ite_cond_eq_false]
          rw [add_comm]
          convert h using 3
          <;>
          group
          congr 1
          trivial
          trivial
        · rw [ite_cond_eq_false]
          · suffices y i ≤ 1 + x i by
              have h5 : 5 + i = i := by
                apply zero_add
              rw [h5]
              simp [hi.1] at this
              exact this
            apply y_le_one_add_x
            assumption
          · simp
            push_neg
            trivial

  -- These conditions clearly hold at the beginning of the first round, when all buckets are empty. Assume that Cinderella manages to maintain them until the beginning of the $r$-th round $(r \geq 1)$.
  -- By induction, she thus manages to maintain them at the beginning of every round. In particular she manages to keep the contents of every single bucket at most 1 liter. Therefore, the buckets of 2-liter capacity will never overflow.
  replace key : ∀ y : State, ∃ x' : State, x' ∈ Cindrella_move y ∧ ((∃ x : State, Cindrella_condition x ∧ y ∈ Stepmother_move x) → Cindrella_condition x') := by
    intro y
    by_cases h : ∃ x : State, Cindrella_condition x ∧ y ∈ Stepmother_move x
    · obtain ⟨x, hx⟩ := h
      obtain ⟨x', hx'⟩ := key x hx.1 y hx.2
      use x'
      constructor
      · exact hx'.1
      · intro _
        exact hx'.2
    · let x' : State | 0 => 0 | 1 => 0 | j => y j
      use x'
      constructor
      · use 0
        simp [x']
      · intro _
        contradiction
  
  obtain ⟨f, hf⟩ := Classical.skolem.mp key

  let s : Cindrella_strategy := fun y => ⟨f y, (hf y).1⟩

  use s

  intro t

  suffices ∀ n : ℕ, Cindrella_condition (game s t (2 * n)) by
    intro n
    simp [game]
    obtain ⟨i,hc⟩ := this n
    set x := game s t (2 * n)
    set y := (t x).val
    intro j
    apply le_trans
    exact y_le_one_add_x x y (t x).prop j
    rw [(by norm_num : (2 : NNReal) = 1 + 1)]
    rw [add_le_add_iff_left]
    rcases mod_five_exhaust i j with (h|h|h|h|h) <;>
    rw [h]
    · rw [hc.1]
      norm_num
    · rw [hc.2.1]
      norm_num
    · replace hc := hc.2.2.1
      apply le_trans
      show x (i + 2) ≤ x (i + 2) + x (i + 4)
      simp
      exact hc
    · exact hc.2.2.2
    · replace hc := hc.2.2.1
      apply le_trans
      show x (i + 4) ≤ x (i + 2) + x (i + 4)
      simp
      exact hc

  intro n
  induction n
  case zero =>
    simp [game]
    use 0
    simp
  case succ n ih =>
    set x := game s t (2 * n)
    set y := (t x).val
    replace hf := hf y
    convert (hf.2 ⟨x, ⟨ih, (t x).prop⟩⟩ : Cindrella_condition (f y))
    rw [(by ring : 2 * (n + 1) = (2 * n + 1) + 1)]
    rw [game]
    simp
    rw [game]
    rw [ite_cond_eq_true]
    simp