import Mathlib

theorem algebra_602762 (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0)
    (h1 : x^2 + x * y + y^2 / 3 = 25) (h2 : y^2 / 3 + z^2 = 9) (h3 : z^2 + z * x + x^2 = 16) :
    x * y + 2 * y * z + 3 * z * x = 24 * Real.sqrt 3 := by
  have h6 : (x * y + 2 * y * z + 3 * z * x) ^ 2 = 1728 := by
    nlinarith [sq_nonneg (x - y * Real.sqrt 3 / 2), sq_nonneg (y - 2 * z), sq_nonneg (z - x * Real.sqrt 3 / 2),
      Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num),
      Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  have h7 : (x * y + 2 * y * z + 3 * z * x) = 24 * Real.sqrt 3 := by
    have h8 : (x * y + 2 * y * z + 3 * z * x) > 0 := by
      nlinarith
    have h9 : (24 * Real.sqrt 3) > 0 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    have h10 : ((x * y + 2 * y * z + 3 * z * x)) ^ 2 = (24 * Real.sqrt 3) ^ 2 := by
      linarith [h6, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    have h11 : (x * y + 2 * y * z + 3 * z * x) = 24 * Real.sqrt 3 := by
      nlinarith [h10, h8, h9]
    linarith
  linarith