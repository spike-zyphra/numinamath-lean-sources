import Mathlib

theorem algebra_1435 : (|( (-355 / 113 : ℝ) - abs (-355 / 113) )|) / (-355 / 113) = -2 := by
  have h1 : abs (-355 / 113 : ℝ) = 355 / 113 := by
    norm_num [abs_of_nonneg, abs_of_nonpos]
  rw [h1]
  norm_num [abs_of_nonneg, abs_of_nonpos]