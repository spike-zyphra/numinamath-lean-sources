import Mathlib

theorem inequalities_601219 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x^2 + y^2 + z^2 ≤ Real.sqrt 3 * x * y * z) :
    x + y + z ≤ x * y * z := by 
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), 
          sq_nonneg (x + y + z - x * y * z), sq_nonneg (x * y * z - (x + y + z)), 
          Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), 
          mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, 
          sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y)
          ]