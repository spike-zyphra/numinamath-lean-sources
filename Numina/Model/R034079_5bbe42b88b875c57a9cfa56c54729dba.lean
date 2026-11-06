import Mathlib

theorem algebra_317625 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h1 : x^2 + x * y + (y^2) / 3 = 25) (h2 : (y^2) / 3 + z^2 = 9) (h3 : z^2 + x * z + x^2 = 16) :
    x * y + 2 * y * z + 3 * x * z = 24 * Real.sqrt 3 := by
  have h4 : (x * y + 2 * y * z + 3 * x * z) ^ 2 = 1728 := by
    nlinarith [sq_nonneg (x - y * Real.sqrt 3 / 2), sq_nonneg (y - 3 * Real.sqrt 3), sq_nonneg (z - 3 / 2 * Real.sqrt 3),
      Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num : (0 : ℝ) < 3),
      Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num : (0 : ℝ) ≤ 3),
      mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]
  have h5 : x * y + 2 * y * z + 3 * x * z = Real.sqrt 1728 := by
    have h8 : (x * y + 2 * y * z + 3 * x * z) ^ 2 = 1728 := h4
    have h9 : 0 ≤ x * y + 2 * y * z + 3 * x * z := by
      positivity
    have h10 : x * y + 2 * y * z + 3 * x * z = Real.sqrt 1728 := by
      rw [←h8]
      field_simp [Real.sqrt_sq (show 0 ≤ x * y + 2 * y * z + 3 * x * z by positivity)]
      all_goals linarith
    exact h10
  have h6 : Real.sqrt 1728 = 24 * Real.sqrt 3 := by
    calc
      Real.sqrt 1728 = Real.sqrt (24^2 * 3) := by
        norm_num
      _ = (Real.sqrt (24^2)) * Real.sqrt 3 := by
        rw [Real.sqrt_mul (by norm_num)]
      _ = (24 * Real.sqrt 1) * Real.sqrt 3 := by
        rw [Real.sqrt_sq (by norm_num)]
        all_goals norm_num
      _ = (24 * 1) * Real.sqrt 3 := by
        rw [Real.sqrt_one]
        all_goals norm_num
      _ = 24 * Real.sqrt 3 := by
        ring_nf
        all_goals norm_num
  rw [h6] at h5
  linarith