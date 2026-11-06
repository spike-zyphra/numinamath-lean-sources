import Mathlib

theorem inequalities_229081 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x * y * z = 1) :
    27 ≤ (2 + x) * (2 + y) * (2 + z) := by 
  nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1),
      sq_nonneg (x * y * z - 1), h, mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]