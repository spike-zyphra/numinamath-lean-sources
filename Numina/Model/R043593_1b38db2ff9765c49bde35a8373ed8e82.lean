import Mathlib

theorem algebra_323648 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h1 : x^2 + x * y + y^2 / 3 = 25) (h2 : y^2 / 3 + z^2 = 9) (h3 : z^2 + z * x + x^2 = 16) :
    x * y + 2 * y * z + 3 * z * x = 24 * Real.sqrt 3 := by
  have h4 : 3 * x^2 + 3 * x * y + y^2 = 75 := by
    nlinarith
  have h5 : y^2 + 3 * z^2 = 27 := by
    nlinarith
  have h6 : (x * y + 2 * y * z + 3 * z * x) ^ 2 = 1728 := by
    nlinarith [sq_nonneg (x - y * Real.sqrt 3 / 3), sq_nonneg (y - Real.sqrt 3 * z), sq_nonneg (z - x * Real.sqrt 3 / 3), Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  have h6' : (x * y + 2 * y * z + 3 * z * x) = Real.sqrt 1728 := by
    have h82 : (x * y + 2 * y * z + 3 * z * x) ≥ 0 := by positivity
    have h83 : (Real.sqrt 1728) ^ 2 = 1728 := by
      rw [Real.sq_sqrt]
      linarith
    have h84 : (x * y + 2 * y * z + 3 * z * x) = Real.sqrt 1728 := by
      have h85 : (x * y + 2 * y * z + 3 * z * x) ≥ 0 := by positivity
      have h86 : (Real.sqrt 1728) ≥ 0 := by positivity
      nlinarith [Real.sqrt_nonneg 1728, sq_nonneg (x * y + 2 * y * z + 3 * z * x - Real.sqrt 1728), Real.sq_sqrt (show (0 : ℝ) ≤ (1728 : ℝ) by norm_num)]
    linarith
  have h7 : Real.sqrt 1728 = 24 * Real.sqrt 3 := by
    have h82 : Real.sqrt 1728 = 24 * Real.sqrt 3 := by
      rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
      <;> ring_nf <;> norm_num
    linarith
  rw [h7] at h6'
  linarith