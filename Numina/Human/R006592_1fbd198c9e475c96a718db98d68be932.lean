import Mathlib
/-
Let $n$ and $m$ be positive integers.
Prove that any non-negative integer $a$ such that
$a \le m \cdot n!$ can be represented as a sum of
$k$ distinct natural numbers, where $k \le n$,
and each of these $k$ numbers
is a divisor of $m \cdot n!$.
-/

-- Theorem: Counterexample to the claim that every integer a ≤ m * n! can be represented 
-- as a sum of at most n distinct divisors of m * n!
theorem number_theory_638963 (ha : ∀ n m : ℕ, ∀ a ≤ m * n.factorial, ∃ xs, xs.card ≤ n ∧ xs.sum id = a ∧ xs ⊆ (m * n.factorial).divisors) : False := by
  -- We construct a counterexample: n = 1, m = 3, a = 2
  -- This shows that 2 cannot be represented as a sum of at most 1 distinct divisor of 3 * 1! = 3
  have counter : ∃ n m a, a ≤ m * (Nat.factorial n) ∧ 
    ¬∃ xs : Finset ℕ, (xs.card ≤ n ∧ xs.sum id = a ∧ xs ⊆ Nat.divisors (m * (Nat.factorial n))) := by
    use 1, 3, 2
    constructor
    · -- Prove that 2 ≤ 3 * 1! = 3
      simp [Nat.factorial]
    · -- Prove that no set satisfies the required conditions
      simp [Nat.factorial]
      -- The divisors of 3 * 1! = 3 are {1, 3}
      have divisors_eq : Nat.divisors 3 = {1, 3} := by
        rfl
      rw [divisors_eq]
      -- Assume for contradiction that such a set xs exists
      intro xs h_card h_sum h_subset
      -- xs can only contain elements from {1, 3}
      have xs_subset : xs ⊆ {1, 3} := h_subset
      -- xs has at most 1 element
      have card_le_one : xs.card ≤ 1 := h_card
      -- The sum of elements in xs equals 2
      have sum_eq_two : xs.sum id = 2 := h_sum
      
      -- Case analysis on the cardinality of xs
      cases' Nat.lt_or_eq_of_le card_le_one with h h
      · -- Case 1: xs.card = 0, so xs = ∅ and sum = 0 ≠ 2
        have : xs.card = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_succ_le_succ h)
        have : xs = ∅ := Finset.card_eq_zero.mp this
        rw [this] at sum_eq_two
        simp at sum_eq_two
      · -- Case 2: xs.card = 1, so xs = {x} for some x ∈ {1, 3}
        have card_eq_one : xs.card = 1 := h
        obtain ⟨x, hx⟩ := Finset.card_eq_one.mp card_eq_one
        rw [hx] at sum_eq_two h_subset
        simp at sum_eq_two h_subset
        -- But x ∈ {1, 3} and x = 2 is impossible
        omega
  
  -- Extract the counterexample and derive contradiction
  obtain ⟨n, m, a, ha_bound, ha_neg⟩ := counter
  -- Apply the hypothesis ha to get a set xs that should satisfy the conditions
  obtain ⟨xs, hxs⟩ := ha n m a ha_bound
  -- But this contradicts our counterexample
  exact ha_neg ⟨xs, hxs⟩