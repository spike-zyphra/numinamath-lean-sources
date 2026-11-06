import Mathlib

open Real

theorem inequalities_155863 (n : ℕ) (hn : n > 2) : 5^n > 4^n + 3^n := by
  have h1 : n ≥ 3 := by linarith
  have h2 : ∀ (n : ℕ), n ≥ 3 → 5 ^ n > 4 ^ n + 3 ^ n := by
    intro n hn1
    have base3 : 5 ^ 3 > 4 ^ 3 + 3 ^ 3 := by norm_num
    have step : ∀ (k : ℕ), k ≥ 3 → 5 ^ k > 4 ^ k + 3 ^ k → 5 ^ (k + 1) > 4 ^ (k + 1) + 3 ^ (k + 1) := by
      intro k hk h1
      have h2 : (5 : ℕ) ^ (k + 1) = 5 * (5 ^ k) := by ring
      have h3 : (4 : ℕ) ^ (k + 1) + (3 : ℕ) ^ (k + 1) = 4 * (4 ^ k) + 3 * (3 ^ k) := by ring
      rw [h2, h3]
      have h4 : 5 * (5 ^ k) > 5 * ((4 : ℕ) ^ k + (3 : ℕ) ^ k) := by
        have h5 : (5 ^ k) > (4 ^ k + 3 ^ k) := h1
        exact Nat.mul_lt_mul_of_pos_left h5 (by norm_num)
      have h5 : 5 * ((4 : ℕ) ^ k + (3 : ℕ) ^ k) ≥ (4 * (4 ^ k) + 3 * (3 ^ k)) := by
        nlinarith [show (4 : ℕ) ^ k > 0 by positivity, show (3 : ℕ) ^ k > 0 by positivity]
      linarith [h4, h5]
    exact Nat.le_induction base3 step n hn1
  have h3 : 5 ^ n > 4 ^ n + 3 ^ n := h2 n h1
  exact h3