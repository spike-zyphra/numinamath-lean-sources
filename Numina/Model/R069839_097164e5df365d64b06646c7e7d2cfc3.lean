import Mathlib

theorem algebra_4363 {x y : ℝ} (h : (x - y + 6) ^ 2 + (10 - x + y) ^ 2 = 132) : (x - y + 6) * (10 - x + y) = 62 := by
  nlinarith [sq_nonneg ((x - y + 6) + (10 - x + y)), sq_nonneg ((x - y + 6) - (10 - x + y)), sq_nonneg (x - y + 6), sq_nonneg (10 - x + y)]