import Mathlib

theorem algebra_124556 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h1 : x ^ 2 + x * y + (1 / 3) * y ^ 2 = 25) (h2 : (1 / 3) * y ^ 2 + z ^ 2 = 9)
    (h3 : z ^ 2 + x * z + x ^ 2 = 16) :
    x * y + 2 * y * z + 3 * z * x = 24 * Real.sqrt 3 := by
  have h4 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h5 : (x * y + 2 * y * z + 3 * z * x) ^ 2 = 1728 := by
    nlinarith [sq_nonneg (x - y * Real.sqrt 3 / 3), sq_nonneg (y - z * Real.sqrt 3), sq_nonneg (z - x * Real.sqrt 3), Real.sqrt_nonneg 3, h4]
  have h6 : (x * y + 2 * y * z + 3 * z * x) = Real.sqrt 1728 := by
    have h7 : (x * y + 2 * y * z + 3 * z * x) ≥ 0 := by
      positivity
    have h8 : Real.sqrt 1728 ≥ 0 := by
      positivity
    have h9 : Real.sqrt 1728 ^ 2 = 1728 := by
      rw [Real.sq_sqrt]
      all_goals linarith
    have h10 : (x * y + 2 * y * z + 3 * z * x) ^ 2 = Real.sqrt 1728 ^ 2 := by
      rw [h5]
      rw [h9]
    have h11 : Real.sqrt 1728 ≥ 0 := by
      positivity
    have h12 : (x * y + 2 * y * z + 3 * z * x) ≥ 0 := by
      positivity
    nlinarith
  have h7 : Real.sqrt 1728 = 24 * Real.sqrt 3 := by
    calc
      Real.sqrt 1728 = Real.sqrt (24 ^ 2 * 3) := by
        norm_num
      _ = (24 : ℝ) * Real.sqrt 3 := by
        rw [Real.sqrt_mul (by norm_num)]
        rw [Real.sqrt_sq (by norm_num)]
      _ = 24 * Real.sqrt 3 := by
        ring
  rw [h7] at h6
  linarith