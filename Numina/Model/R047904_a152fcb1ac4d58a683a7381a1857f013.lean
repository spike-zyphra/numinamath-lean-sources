import Mathlib

theorem inequalities_123365 (n : ℕ) (h : n > 4) : 2^n > n^2 := by
  have h1 : ∀ (n : ℕ), n ≥ 5 → 2 ^ n > n ^ 2 := by
    intro n hn
    have h2 : n ≥ 5 := hn
    have base5 : 2 ^ 5 > 5 ^ 2 := by norm_num
    have step5 : ∀ (k : ℕ), k ≥ 5 → 2 ^ k > k ^ 2 → 2 ^ (k + 1) > (k + 1) ^ 2 := by
      intro k hk h
      have h3 : 2 ^ (k + 1) = 2 * (2 ^ k) := by ring
      have h4 : 2 * (2 ^ k) > 2 * (k ^ 2) := by
        have : 2 ^ k > k ^ 2 := h
        nlinarith
      have h5 : 2 * (k ^ 2) ≥ (k + 1) ^ 2 := by
        nlinarith [sq_nonneg (k), sq_nonneg (k - 2), sq_nonneg (k - 1), sq_nonneg (k - 3), sq_nonneg (k - 4)]
      have h6 : 2 * (2 ^ k) > (k + 1) ^ 2 := by
        nlinarith [h4, h5]
      linarith [h3, h6]
    exact Nat.le_induction base5 step5 n h2
  have hn5 : n ≥ 5 := by
    linarith
  have h2 : 2 ^ n > n ^ 2 := by
    apply h1 n hn5
  exact h2