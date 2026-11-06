import Mathlib

theorem algebra_301481 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h1 : x^2 + x * y + y^2 / 3 = 25) (h2 : y^2 / 3 + z^2 = 9) (h3 : z^2 + z * x + x^2 = 1) :
    x * y + 2 * y * z + 3 * z * x = 24 * Real.sqrt 3 := by

  have h4 : (x * y + 2 * y * z + 3 * z * x) ^ 2 = 576 * 3 := by
    nlinarith [sq_nonneg (x - y * Real.sqrt 3 / 2), sq_nonneg (y / Real.sqrt 3 - z * 2), sq_nonneg (z - x * Real.sqrt 3 / 2),
      Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num),
      Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]

  have h5 : (x * y + 2 * y * z + 3 * z * x) > 0 := by
    nlinarith [mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]

  have h6 : x * y + 2 * y * z + 3 * z * x = Real.sqrt (576 * 3) := by
    have h7 : (x * y + 2 * y * z + 3 * z * x) ≥ 0 := by linarith
    have h8 : Real.sqrt (576 * 3) ≥ 0 := by positivity
    have h9 : (Real.sqrt (576 * 3)) ^ 2 = 576 * 3 := Real.sq_sqrt (by norm_num)
    nlinarith [h4, Real.sqrt_nonneg (576 * 3)]

  have h7 : Real.sqrt (576 * 3) = 24 * Real.sqrt 3 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf
    <;> norm_num [Real.sq_sqrt]

  rw [h6, h7]