import Mathlib

theorem algebra_306755 {x y : ℝ} (h1 : x / (3^3 + 4^3) + y / (3^3 + 6^3) = 1)
    (h2 : x / (5^3 + 4^3) + y / (5^3 + 6^3) = 1) : x + y = 432 := by
  norm_num at h1 h2
  linarith