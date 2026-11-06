import Mathlib

theorem inequalities_82348 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    (12 * x ^ 2 + y * z) * (12 * y ^ 2 + x * z) * (12 * z ^ 2 + x * y) ≠ 2014 * x ^ 2 * y ^ 2 * z ^ 2 := by
  intro h
  nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y), 
          sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), 
          sq_nonneg (x * (x - y)), sq_nonneg (x * (x - z)), 
          sq_nonneg (y * (y - x)), sq_nonneg (y * (y - z)), 
          sq_nonneg (z * (z - x)), sq_nonneg (z * (z - y)), 
          mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, 
          mul_pos (show 0 < x * y from mul_pos hx hy) (show 0 < y * z from mul_pos hy hz), 
          mul_pos (show 0 < x * y from mul_pos hx hy) (show 0 < x * z from mul_pos hx hz), 
          mul_pos (show 0 < x * z from mul_pos hx hz) (show 0 < y * z from mul_pos hy hz)]