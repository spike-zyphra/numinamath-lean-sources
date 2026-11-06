import Mathlib

theorem algebra_103258 (n : ℕ) (hn : n > 0) (h : 8^4 = 4^n) : n = 6 := by
  have h1 : (8 : ℕ) ^ 4 = 2 ^ 12 := by
    norm_num
  have h2 : (4 : ℕ) ^ n = 2 ^ (2 * n) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
    rw [← pow_mul]
    all_goals linarith
  rw [h1, h2] at h
  have h3 : 12 = 2 * n := by
    exact Nat.pow_right_injective (by norm_num) h
  have h4 : n = 6 := by
    linarith
  exact h4