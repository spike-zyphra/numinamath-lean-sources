import Mathlib

theorem algebra_235408 : max (max (max (max (1 - 0.1 : ℝ) (1 - 0.01)) (1 - 0.001)) (1 - 0.0001)) (1 - 0.00001) = 1 - 0.00001 := by
  norm_num [max_eq_right, max_eq_left]