import Mathlib

theorem algebra_320610 {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h1 : x^2 + x * y + (1 / 3) * y^2 = 25) (h2 : (1 / 3) * y^2 + z^2 = 9) (h3 : z^2 + x * z + x^2 = 16) :
    x * y + 2 * y * z + 3 * z * x = 24 * Real.sqrt 3 := by
  have h5 : (x * y + 2 * y * z + 3 * z * x) ^ 2 = (24 * Real.sqrt 3) ^ 2 := by 
    nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), sq_nonneg (x - z), sq_nonneg (y - z * Real.sqrt 3), sq_nonneg (x * z - z^2 * Real.sqrt 3), sq_nonneg (x * y - z * (x + 2 * z)), Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num : (3 : ℝ) > (0 : ℝ)), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]
  have h6 : x * y + 2 * y * z + 3 * z * x = 24 * Real.sqrt 3 := by
    nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (3 : ℝ) ≥ (0 : ℝ)), Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num : (3 : ℝ) > (0 : ℝ)), sq_nonneg (x * y + 2 * y * z + 3 * z * x - 24 * Real.sqrt 3), h5, mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]
  exact h6