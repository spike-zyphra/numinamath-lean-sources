import Mathlib

theorem algebra_322076 (x y : ℝ) (h : 2 * x ^ 2 + 3 * y ^ 2 = 4 * x) : x + y ≥ 1 - Real.sqrt 15 / 3 := by
  nlinarith [sq_nonneg (x - (5 - Real.sqrt 15) / 5), sq_nonneg (y + 2 * Real.sqrt 15 / 15),
    sq_nonneg (x - 1 + y + Real.sqrt 15 / 3),
    sq_nonneg ((x - (1 - Real.sqrt 15 / 3)) * 5),
    sq_nonneg ((y + 2 * Real.sqrt 15 / 15) * 5),
    Real.sqrt_pos.mpr (by norm_num : (15 : ℝ) > 0),
    Real.sq_sqrt (show (0 : ℝ) ≤ (15 : ℝ) by norm_num),
    Real.sqrt_nonneg 15, sq_nonneg (Real.sqrt 15 ^ 2 - 15),
    mul_nonneg (Real.sqrt_nonneg 15) (Real.sqrt_nonneg 15)
  ]