import Mathlib
set_option maxHeartbeats 800000
theorem algebra_121038 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h1 : x^2 + x * y + y^2 / 3 = 25) (h2 : y^2 / 3 + z^2 = 9) (h3 : z^2 + z * x + x^2 = 16) :
    x * y + 2 * y * z + 3 * z * x = 24 * Real.sqrt 3 := by
  have h4 : (x * y + 2 * y * z + 3 * z * x) ^ 2 = 576 * 3 := by
    nlinarith [sq_nonneg (x - z * Real.sqrt 3 / 2), sq_nonneg (y - z * 3), sq_nonneg (z - 2), sq_nonneg (x * z), sq_nonneg (y * x - z * 9), sq_nonneg (y ^ 2 - 27), sq_nonneg (x ^ 2 - 12), Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  have h5 : x * y + 2 * y * z + 3 * z * x ≥ 0 := by
    nlinarith [mul_pos hx hy, mul_pos hy hz, mul_pos hz hx]
  have h6 : x * y + 2 * y * z + 3 * z * x = Real.sqrt 1728 := by
    have h7 : (x * y + 2 * y * z + 3 * z * x) ^ 2 = 1728 := by
      nlinarith
    have h8 : x * y + 2 * y * z + 3 * z * x ≥ 0 := by
      nlinarith [mul_pos hx hy, mul_pos hy hz, mul_pos hz hx]
    have h9 : (x * y + 2 * y * z + 3 * z * x) = Real.sqrt 1728 := by
      rw [←h7]
      field_simp [h8]
    linarith
  have h7 : Real.sqrt 1728 = 24 * Real.sqrt 3 := by
    calc
      Real.sqrt 1728 = Real.sqrt (576 * 3) := by norm_num
      _ = Real.sqrt (24 ^ 2 * 3) := by norm_num
      _ = (24 : ℝ) * Real.sqrt 3 := by
        rw [Real.sqrt_mul (by norm_num)]
        rw [Real.sqrt_sq (by norm_num)]
        <;> ring_nf <;> norm_num
  rw [h7] at h6
  linarith