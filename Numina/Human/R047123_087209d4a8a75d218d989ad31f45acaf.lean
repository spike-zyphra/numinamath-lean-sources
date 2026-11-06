import Mathlib

theorem inequalities_600113
    (x y z : ℝ)
    (hx : 0 < x)
    (hy : 0 < y)
    (hz : 0 < z) :
    x^3 + y^3 + z^3 ≥ 3 * x * y * z + x * (y - z)^2 + y * (z - x)^2 + z * (x - y)^2 := by 
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
    sq_nonneg (x - y + z), sq_nonneg (y - z + x), sq_nonneg (z - x + y),
    sq_nonneg (x - y - z), sq_nonneg (y - z - x), sq_nonneg (z - x - y),
    mul_pos hx hy, mul_pos hy hz, mul_pos hx hz]