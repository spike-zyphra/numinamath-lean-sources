import Mathlib
set_option maxHeartbeats 800000
theorem inequalities_601452 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x + y + z + x^2 + y^2 + z^2 = 6) :
    x^2 * y + y^2 * z + z^2 * x ≤ 3 := by
  nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1),
      sq_nonneg (x + y + z - 3), sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      mul_pos hx hy, mul_pos hx hz, mul_pos hy hz
  ]