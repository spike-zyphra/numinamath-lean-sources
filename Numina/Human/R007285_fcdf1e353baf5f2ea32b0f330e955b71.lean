import Mathlib

theorem inequalities_221986 (x y : ℝ) : (x + y) ^ 4 ≤ 8 * (x ^ 4 + y ^ 4) := by 
  nlinarith [sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x - y)]