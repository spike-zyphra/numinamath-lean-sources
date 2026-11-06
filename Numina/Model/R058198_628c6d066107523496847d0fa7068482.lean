import Mathlib

theorem algebra_602533 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x * y * z * (x + y + z) = 1) :
    2 ≤ (x + y) * (x + z) := by
  nlinarith [sq_nonneg (x * y - 1), sq_nonneg (x * z - 1), sq_nonneg (y * z - 1),
          sq_nonneg (x * (y + z) - 1), sq_nonneg (y - z), 
          mul_pos hx hy, mul_pos hx hz, mul_pos hy hz
         ]