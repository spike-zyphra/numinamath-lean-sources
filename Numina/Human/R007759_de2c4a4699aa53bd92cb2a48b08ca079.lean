import Mathlib

theorem number_theory_285108 (n : ℕ) (h : n = 12) :
    n * (1 - (1 / 2 : ℚ) * (2 / 3 : ℚ)) = 8 := by
  subst n
  norm_num