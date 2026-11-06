import Mathlib

theorem algebra_308752 (a b : ℝ) :
  2*a^2 - 8*a*b + 17*b^2 - 16*a - 4*b + 1998 ≥ 1930 := by 
    nlinarith [sq_nonneg (a - 2 * b - 4), sq_nonneg (b - 2)]