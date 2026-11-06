import Mathlib

theorem number_theory_288097 (k : ℕ) (hk : 0 < k) :
    ∃ a d, ∀ n, a + d * n > 0 ∧ (a + d * n).divisors.card % k = 0 := by
  use 2 ^ (k - 1)
  use 0
  intro n
  constructor
  ·
    -- Show $a + 0 \cdot n > 0$.
    have h1 : 2 ^ (k - 1) > 0 := by
      apply Nat.pow_pos
      all_goals norm_num
    have h2 : 2 ^ (k - 1) + 0 * n > 0 := by
      linarith [h1]
    linarith [h2]
  ·
    -- Show $(a + 0 \cdot n).divisors.card \mod k = 0$.
    have h3 : (2 ^ (k - 1)).divisors.card = k := by
      rw [Nat.divisors_prime_pow]
      . -- The number of divisors of 2^(k-1) is (k-1)+1 = k
        simp
        all_goals
        try { 
          omega 
        }
      all_goals -- Check side conditions.
        norm_num
    have h4 : (2 ^ (k - 1) + 0 * n).divisors.card = k := by
      have h5 : (2 ^ (k - 1) + 0 * n) = 2 ^ (k - 1) := by 
        ring
      rw [h5]
      exact h3
    rw [h4]
    simp