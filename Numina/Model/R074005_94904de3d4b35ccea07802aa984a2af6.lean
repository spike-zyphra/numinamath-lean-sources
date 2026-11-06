import Mathlib

theorem inequalities_308698 (n : ℕ) (h₀ : n > 4) : 2^n > n^2 := by
  have h1 : n ≥ 5 := by linarith
  have baseCase : 2 ^ 5 > 5 ^ 2 := by norm_num
  have inductionStep : ∀ k : ℕ, k ≥ 5 → 2 ^ k > k ^ 2 → 2 ^ (k + 1) > (k + 1) ^ 2 := by
    intro k hk h
    have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    rw [h2]
    have h3 : 2 * 2 ^ k > 2 * k ^ 2 := by
      nlinarith [h]
    have h4 : 2 * k ^ 2 ≥ (k + 1) ^ 2 := by
      nlinarith [sq_nonneg (k - 1 : ℕ), sq_nonneg (k - 2 : ℕ), sq_nonneg (k - 5 : ℕ), show k ≥ 5 by linarith]
    linarith [h3, h4]
  exact Nat.le_induction baseCase inductionStep n h1