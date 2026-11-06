import Mathlib

theorem inequalities_601797 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x + y + z = x * y * z) :
    x ^ 2 + y ^ 2 + z ^ 2 - 2 * (x * y + y * z + z * x) + 9 ≥ 0 := by 
  nlinarith [sq_nonneg (x - y - z), sq_nonneg (y - x - z), sq_nonneg (z - x - y), 
          sq_nonneg (x + y + z - 3), sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
          mul_pos hx hy, mul_pos hy hz, mul_pos hz hx, 
          mul_pos (show 0 < x * y by nlinarith) (show 0 < z by linarith)]