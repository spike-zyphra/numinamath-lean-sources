import Mathlib

theorem inequalities_208441 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    x ^ 4 + y ^ 4 + z ^ 2 ≥ x * y * z * 8 ^ ((1 : ℝ) / 2) := by 
  have h1 : (8 : ℝ) ^ ((1 : ℝ) / 2) = Real.sqrt (8 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
  have h2 : Real.sqrt (8 : ℝ) = 2 * Real.sqrt 2 := by 
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num
  have h3 : (8 : ℝ) ^ ((1 : ℝ) / 2) = 2 * Real.sqrt 2 := by
    rw [h1, h2]
  rw [h3]
  nlinarith [sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x ^ 2 - y * z), sq_nonneg (y ^ 2 - x * z), sq_nonneg (z - 2 * x * y / (2 : ℝ)), sq_nonneg (x - y), sq_nonneg (x^2 - y^2), sq_nonneg (x * y - (z)), sq_nonneg (x * y - z / (2 : ℝ)), Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (z^2 - 2 * x^2 * y^2), sq_nonneg (x * y * Real.sqrt 2 - z), sq_nonneg ((x ^ 2 * y ^ 2) - z ^ 2), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, mul_pos (mul_pos hx hy) hz, Real.sqrt_nonneg 2, sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x ^ 2 - z), sq_nonneg (y ^ 2 - z)]