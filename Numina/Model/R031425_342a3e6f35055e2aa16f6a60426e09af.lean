import Mathlib

theorem algebra_307119 (n : ℕ) (hn : n > 0) :
    IsSquare (n ^ 4 + 2 * n ^ 3 + 5 * n ^ 2 + 12 * n + 5) ↔ n = 1 ∨ n = 2 := by
  constructor
  · -- Assume it's a perfect square, prove n = 1 or 2
    intro h
    rcases h with ⟨k, hk⟩
    by_cases h1 : n ≤ 2
    · -- n is 1 or 2
      interval_cases n <;> norm_num at hk ⊢
      <;> try trivial
      <;> try { 
        have : k ≤ 10 := by nlinarith
        interval_cases k <;> omega 
      }
    · -- n > 2
      have h2 : n > 2 := by omega
      have h5 : (n ^ 2 + n + 1) ^ 2 < n ^ 4 + 2 * n ^ 3 + 5 * n ^ 2 + 12 * n + 5 := by
        nlinarith [sq_nonneg (n + 1), sq_nonneg (n - 2), sq_nonneg (n + 2), sq_nonneg (n * (n - 2)), h2]
      have h4 : n ^ 4 + 2 * n ^ 3 + 5 * n ^ 2 + 12 * n + 5 < (n ^ 2 + n + 3) ^ 2 := by
        nlinarith [sq_nonneg (n + 1), sq_nonneg (n - 2), sq_nonneg (n + 2), sq_nonneg (n * (n - 2)), h2]
      have h6 : (n ^ 2 + n + 1) < k := by
        nlinarith [h5, hk]
      have h7 : k < (n ^ 2 + n + 3) := by
        nlinarith [h4, hk]
      have h8 : k = (n ^ 2 + n + 2) := by
        omega
      rw [h8] at hk
      nlinarith [sq_nonneg (n + 2), sq_nonneg (n * (n - 1)), sq_nonneg (n * (n - 2)), sq_nonneg (n * n), sq_nonneg (k * k), h2, h8]
  · -- Assume n = 1 or 2, prove it's a perfect square
    rintro (h | h)
    · -- n = 1
      rw [h]
      use 5
      all_goals
        nlinarith
    · -- n = 2
      rw [h]
      use 9
      all_goals
        nlinarith