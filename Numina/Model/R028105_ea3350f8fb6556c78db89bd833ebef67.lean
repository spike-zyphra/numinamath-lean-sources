import Mathlib

theorem algebra_137469 {n : ℕ} (h : n^3 = 2012^12) :
    n * (2012^11)^2 = 2012^26 := by
  have h1 : n = 2012^4 := by
    have h2 : n^3 = 2012^12 := h
    have h3 : n^3 = (2012^4) ^ 3 := by
      norm_num [h2]
    have h4 : n = 2012^4 := by
      have h5 : n ^ 3 = (2012 ^ 4) ^ 3 := h3
      exact Nat.pow_left_injective (by norm_num) h5
    exact h4
  rw [h1]
  all_goals norm_num