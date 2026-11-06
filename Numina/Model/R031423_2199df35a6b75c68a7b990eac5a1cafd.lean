import Mathlib

theorem inequalities_38269 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x ^ 5 + y ^ 5 + z ^ 5 = x * y + y * z + z * x) :
    3 ≥ x ^ 2 * y + y ^ 2 * z + z ^ 2 * x := by

  nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1),
          sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
          sq_nonneg (x^2 - 1), sq_nonneg (y^2 - 1), sq_nonneg (z^2 - 1),
          mul_pos hx hy, mul_pos hy hz, mul_pos hz hx,
          mul_nonneg (mul_nonneg (show 0 ≤ x by linarith) (show 0 ≤ y by linarith)) (show 0 ≤ z by linarith)]