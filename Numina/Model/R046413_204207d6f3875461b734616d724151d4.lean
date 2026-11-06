import Mathlib

theorem algebra_605568 (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) :
  x ^ 2 + x * y ^ 2 + x * y * z ^ 2 ≥ 4 * x * y * z - 4 := by
  nlinarith [sq_nonneg (x - 2), sq_nonneg (y - 2), sq_nonneg (z - 2),
    sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
    mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, 
    mul_pos (show 0 < x by linarith) (show 0 < y * z by nlinarith)
    ]