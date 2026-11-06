import Mathlib

theorem inequalities_103653 (n : ℕ) (h : 4 ≤ n) : 2^n ≥ n^2 := by 
  have h1 : n ≥ 4 := h
  have h2 : 2 ^ n ≥ n ^ 2 := by 
    have base : 2 ^ 4 ≥ 4 ^ 2 := by norm_num 
    have step : ∀ k, k ≥ 4 → 2 ^ k ≥ k ^ 2 → 2 ^ (k + 1) ≥ (k + 1) ^ 2 := by 
      intro k hk h 
      have h1 : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
      rw [h1]
      have h2 : 2 * 2 ^ k ≥ 2 * k ^ 2 := by linarith [h]
      have h3 : 2 * k ^ 2 ≥ (k + 1) ^ 2 := by 
        nlinarith [sq_nonneg (k - 4)]
      linarith 
    exact Nat.le_induction base step n h1 
  exact h2