import Mathlib

theorem inequalities_76422 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x^2 + y^2 + z^2 = x^2 * y^2 + y^2 * z^2 + z^2 * x^2) :
    (x - y)^2 * (y - z)^2 * (z - x)^2 ≤
    2 * ((x^2 - y^2)^2 + (y^2 - z^2)^2 + (z^2 - x^2)^2) := by
  nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y), 
          sq_nonneg (x * y + y * z + z * x), sq_nonneg (x^2 - y^2), sq_nonneg (y^2 - z^2), sq_nonneg (z^2 - x^2),
          sq_nonneg (x * y * z), 
          mul_pos hx hy, mul_pos hy hz, mul_pos hx hz]