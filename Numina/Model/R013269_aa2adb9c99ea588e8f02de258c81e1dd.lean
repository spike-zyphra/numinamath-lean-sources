import Mathlib

theorem algebra_283202 (n : ℕ) (h : n = 5) : n^3 + n - 1 = 129 := by
  subst h
  all_goals norm_num