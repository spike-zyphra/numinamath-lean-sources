import Mathlib

theorem algebra_11678 :
    max (max (max (max (1 / 4 + 1 / 5 : ℚ) (1 / 4 + 1 / 6)) (1 / 4 + 1 / 3)) (1 / 4 + 1 / 8)) (1 / 4 + 1 / 7) = 7 / 12 := by
  norm_num [max_eq_left, max_eq_right]