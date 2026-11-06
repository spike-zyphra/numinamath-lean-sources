import Mathlib

theorem inequalities_5602 (x : ℝ) (hx : x ^ 2 - 5 * x - 24 ≤ 0) : x ≤ 8 := by 
  nlinarith [sq_nonneg (x - 8), sq_nonneg (x + 3)]