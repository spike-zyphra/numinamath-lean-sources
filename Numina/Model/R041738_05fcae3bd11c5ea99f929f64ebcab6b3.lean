import Mathlib

theorem inequalities_603234 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x^2 + y^2 + z^2 ≤ Real.sqrt 3 * x * y * z) :
    x + y + z ≤ x * y * z := by
  nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
          sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
          sq_nonneg (x + y + z - x * y * z),
          Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num),
          mul_pos hx hy, mul_pos hy hz, mul_pos hx hz,
          mul_pos (mul_pos hx hy) hz]