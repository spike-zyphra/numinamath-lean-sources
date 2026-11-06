import Mathlib

theorem algebra_12814 (n : ℕ) (hn : n = 9) :
    n * (n - 1) * 3 / 2 = 108 := by
  subst n
  norm_num