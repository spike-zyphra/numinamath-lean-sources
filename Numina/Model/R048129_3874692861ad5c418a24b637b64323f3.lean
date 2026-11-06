import Mathlib

theorem inequalities_42715 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    x^4 + y^4 + z^2 ≥ x * y * z * Real.sqrt 8 := by
  have h1 : x^4 + y^4 ≥ 2 * x^2 * y^2 := by
    nlinarith [sq_nonneg (x^2 - y^2), sq_nonneg (x^2 + y^2), sq_nonneg (x - y), sq_nonneg (x + y)]
  have h4 : x ^ 4 + y ^ 4 + z ^ 2 ≥ 2 * x ^ 2 * y ^ 2 + z ^ 2 := by linarith [h1]
  have h5 : x^4 + y^4 + z^2 ≥ x * y * z * Real.sqrt 8 := by
    nlinarith [sq_nonneg (z^2 - 2 * x^2 * y^2), sq_nonneg (z - (x * y * Real.sqrt 8 / 2)), sq_nonneg (x^2 - y^2), sq_nonneg (x^2 + y^2), sq_nonneg (x * y * (Real.sqrt 8) / 2 - z), mul_nonneg (show 0 ≤ x^2 by positivity) (show 0 ≤ y^2 by positivity), Real.sqrt_nonneg 8, mul_pos hx hy, Real.sqrt_nonneg 8, Real.sq_sqrt (show (0 : ℝ) ≤ 8 by norm_num), sq_nonneg ((Real.sqrt 8) ^ 2), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  exact h5