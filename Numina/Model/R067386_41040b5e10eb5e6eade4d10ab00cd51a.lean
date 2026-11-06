import Mathlib

theorem inequalities_278815 (n : ℕ) (h₀ : 5 ≤ n) : 2^n > n^2 := by 
  have h1 : n ≥ 5 := h₀
  have base := show 2^5 > 5^2 by norm_num
  have step : ∀ k, k ≥ 5 → 2 ^ k > k ^ 2 → 2 ^ (k + 1) > (k + 1) ^ 2 := by 
    intro k hk h
    have h1 : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    have h2 : 2 * 2 ^ k > 2 * k ^ 2 := by 
      have h3 : 2 ^ k > k ^ 2 := h
      nlinarith
    have h3 : 2 * k ^ 2 ≥ (k + 1) ^ 2 := by 
      nlinarith [sq_nonneg (k - 5 : ℕ), sq_nonneg (k + 1 : ℕ)]
    linarith [h1, h2, h3]
  exact Nat.le_induction base step n h1