import Mathlib

theorem algebra_13993 {x : ℝ} (hx : x > 0) (h : x ^ 2 = 729) : x = 27 := by
  have h1 : x = 27 := by
    nlinarith [sq_nonneg (x - 27), h, sq_nonneg (x + 27), show (27:ℝ) ^ 2 = 729 by norm_num, sq_nonneg (x - 27)]
  exact h1