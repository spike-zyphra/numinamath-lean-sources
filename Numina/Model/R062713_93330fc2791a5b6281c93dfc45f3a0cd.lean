import Mathlib

theorem inequalities_2690 (x y : ℝ) : x ^ 2 + x * y + y ^ 2 ≥ 0 := by
  nlinarith [sq_nonneg (x + y / 2), sq_nonneg y, sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x * y), sq_nonneg (x ^ 2 + y ^ 2)]