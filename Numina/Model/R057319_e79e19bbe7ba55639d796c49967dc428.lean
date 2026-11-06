import Mathlib

theorem algebra_192924 (a b : ℝ) (h : 5 * (a - 1) = b + a ^ 2) : a > b := by 
  nlinarith [sq_nonneg (a - 2)]