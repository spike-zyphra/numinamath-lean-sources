import Mathlib

theorem inequalities_134778 (n : ℕ) (hn : 4 ≤ n) : 2^n ≥ n^2 := by 
  have h1 : n ≥ 4 := by linarith
  have base : 2 ^ 4 ≥ 4 ^ 2 := by norm_num
  have step : ∀ k : ℕ, k ≥ 4 → 2 ^ k ≥ k ^ 2 → 2 ^ (k + 1) ≥ (k + 1) ^ 2 := by 
    intro k hk1 hk2
    have h1 : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    have h2 : 2 * 2 ^ k ≥ 2 * k ^ 2 := by 
      nlinarith [hk2]
    have h3 : 2 * k ^ 2 ≥ (k + 1) ^ 2 := by 
      nlinarith [sq_nonneg (k - 4), sq_nonneg (k - 1)]
    linarith [h1, h2, h3]
  exact Nat.le_induction base step n h1