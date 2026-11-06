import Mathlib

theorem number_theory_95302 (n : ℕ) (h : n = 22 - 12 + 1) :
    33 * n = 363 := by
  subst h
  all_goals norm_num