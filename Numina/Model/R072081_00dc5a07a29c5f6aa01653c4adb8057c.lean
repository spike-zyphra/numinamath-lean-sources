import Mathlib

theorem algebra_101023 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x * y * z * (x + y + z) = 1) :
    2 ≤ (x + y) * (y + z) := by 
  nlinarith [sq_nonneg (x * z - 1), sq_nonneg (y * (x + y + z) - 1),
          mul_pos hx hy, mul_pos hx hz, mul_pos hy hz,
          mul_pos (show 0 < x * y * z by positivity) (show 0 < x + y + z by positivity)]