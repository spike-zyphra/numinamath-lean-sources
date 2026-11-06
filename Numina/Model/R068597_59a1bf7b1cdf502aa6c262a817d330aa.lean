import Mathlib

theorem algebra_302541
    (x y z : ℝ)
    (hx : 0 < x)
    (hy : 0 < y)
    (hz : 0 < z)
    (h1 : x^2 + x * y + y^2 / 3 = 25)
    (h2 : y^2 / 3 + z^2 = 9)
    (h3 : x^2 + x * y + z^2 = 16) :
    x * y + 2 * y * z + 3 * z * x = 24 * Real.sqrt 3 := by
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), sq_nonneg (x - z * Real.sqrt 3), sq_nonneg (y - z * Real.sqrt 3 * 3 / 2), sq_nonneg (y - 2 * z * Real.sqrt 3 / 3), sq_nonneg (x - Real.sqrt 3 * z), sq_nonneg (y - Real.sqrt 3 * 3 / 2 * z), Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]