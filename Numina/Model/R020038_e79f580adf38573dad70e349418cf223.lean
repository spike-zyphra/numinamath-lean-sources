import Mathlib

theorem inequalities_598735 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x^2 + y^2 + z^2 + x * y * z = 4) :
    x + y + z ≤ 3 := by
  nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1),
          sq_nonneg (x * y - 1), sq_nonneg (y * z - 1), sq_nonneg (z * x - 1),
          mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, 
          mul_pos (show 0 < x * y by nlinarith) (show 0 < z by linarith)]