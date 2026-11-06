import Mathlib

open Real

theorem inequalities_601502 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxyz : x * y * z = 1) :
    x ^ 2 + y ^ 2 + z ^ 2 + x + y + z ≥ 2 * (x * y + y * z + z * x) := by

  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
          sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1),
          mul_pos hx hy, mul_pos hy hz, mul_pos hx hz]