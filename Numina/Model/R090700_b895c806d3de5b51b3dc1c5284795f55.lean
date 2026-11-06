import Mathlib

theorem inequalities_106255 (n : ℕ) (hn : 1 ≤ n) : 2^n ≥ n := by
  have h1 : 2 ^ 1 ≥ 1 := by norm_num
  have h2 : ∀ k : ℕ, k ≥ 1 → 2 ^ k ≥ k → 2 ^ (k + 1) ≥ (k + 1) := by
    intro k hk h
    have h3 : 2 ^ (k + 1) = 2 ^ k * 2 := by ring
    have h4 : 2 ^ k * 2 ≥ (k + 1) := by
      nlinarith [sq_nonneg (k : ℕ), sq_nonneg (2 ^ k : ℕ)]
    linarith [h3, h4]
  exact Nat.le_induction h1 h2 n hn