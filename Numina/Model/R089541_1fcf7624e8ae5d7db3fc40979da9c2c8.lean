import Mathlib

open Real

theorem inequalities_8467
    (x y z : ℝ)
    (hx : 0 < x)
    (hy : 0 < y)
    (hz : 0 < z)
    (h : x + y + z = x * y + z * x + y * z) :
    3 ≤ x + y + z := by 
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), 
          sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1),
          mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]