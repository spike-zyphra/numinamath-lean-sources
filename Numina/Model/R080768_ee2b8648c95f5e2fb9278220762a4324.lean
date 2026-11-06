import Mathlib

theorem inequalities_277049 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x + y + z = 1) : x^2 + y^2 + z^2 ≥ 1 / 3 := by 
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
             h, mul_pos hx hy, mul_pos hy hz, mul_pos hz hx]