import Mathlib

theorem inequalities_7862 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    2*(x+y+z)^3+9*x*y*z ≥ 7*(x+y+z)*(x*y+y*z+z*x) := by
  nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
          sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
          sq_nonneg (x * (x - y)), sq_nonneg (x * (x - z)), sq_nonneg (y * (y - x)), sq_nonneg (y * (y - z)), sq_nonneg (z * (z - x)), sq_nonneg (z * (z - y)), 
          mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]