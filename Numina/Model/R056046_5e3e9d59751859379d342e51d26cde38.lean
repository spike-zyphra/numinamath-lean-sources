import Mathlib

theorem algebra_293492 (a b c : ℝ) (h : a^2 + b^2 + c^2 = 4) :
    (a - b)^2 + (b - c)^2 + (c - a)^2 ≤ 12 := by 
  nlinarith [sq_nonneg (a + b + c)]