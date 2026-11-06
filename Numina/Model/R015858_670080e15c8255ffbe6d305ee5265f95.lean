import Mathlib

theorem inequalities_7423 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x^2 + y^2 + z^2 + 2*x*y*z = 1) :
    x + y + z ≤ 3 / 2 := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), 
          sq_nonneg (x + y + z - 3 / 2), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, 
          mul_pos (show 0 < x * y from by nlinarith) (show 0 < z from hz)]