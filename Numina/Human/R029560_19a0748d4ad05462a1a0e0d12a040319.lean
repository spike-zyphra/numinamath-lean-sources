import Mathlib

/-let real numbers x,y satisfy the equation 2x^2+3y^2=4x
Then the minimum value of x+y is ?-/
theorem algebra_322076 (x y : ℝ) (h : 2 * x ^ 2 + 3 * y ^ 2 = 4 * x) : x + y ≥ 1 - Real.sqrt 15 / 3 := by
  nlinarith [sq_nonneg (x - (1 - Real.sqrt 15 / 5)), sq_nonneg (y + 2 * Real.sqrt 15 / 15),
    Real.sq_sqrt (show 0 ≤ 15 by norm_num), 
    Real.sqrt_pos.mpr (show (0:ℝ) < 15 by norm_num),
    mul_self_nonneg (x - 1 + Real.sqrt 15 / 3), mul_self_nonneg (y + 2 * Real.sqrt 15 / 15),
    Real.sq_sqrt (show 0 ≤ (4 * x - 2 * x^2) / 3 by nlinarith [sq_nonneg (x - 1), sq_nonneg y, h])]