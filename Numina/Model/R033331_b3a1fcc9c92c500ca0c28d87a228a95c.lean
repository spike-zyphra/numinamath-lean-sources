import Mathlib

theorem algebra_1434 : max (max (max ((-2) ^ 5 : ℝ) ((-3) ^ 5)) ((-1/2) ^ 5)) ((-1/3) ^ 5) = (-1/3) ^ 5 := by
  norm_num [max_eq_right, max_eq_left]