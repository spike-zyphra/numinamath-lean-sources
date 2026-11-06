import Mathlib

theorem inequalities_1147 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
  (y + z)^2 * (z + x)^2 * (x + y)^2 ≥ 64 / 27 * (x + y + z)^3 * x * y * z := by
  have hx1 : 0 < x * y := mul_pos hx hy
  have hy1 : 0 < y * z := mul_pos hy hz
  have hz1 : 0 < z * x := mul_pos hz hx
  nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
          sq_nonneg (y - z), sq_nonneg (z - x), sq_nonneg (x - y),
          sq_nonneg (x + y + z - 2 * x), sq_nonneg (x + y + z - 2 * y), sq_nonneg (x + y + z - 2 * z),
          mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]