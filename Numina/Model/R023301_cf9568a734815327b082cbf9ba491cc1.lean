import Mathlib

open Real Set

theorem algebra_600252 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hsum : x + y + z = 3) :
    x^2 + y^2 + z^3 ≥ 6 * (2 / 3) - (2 * (2 / 3)^2 + (2 / 3)^3) := by
  have h1 : z = 3 - x - y := by linarith
  rw [h1]
  nlinarith [sq_nonneg (x - y), sq_nonneg (x - (3 - x - y)), sq_nonneg (y - (3 - x - y)), 
          sq_nonneg (x - 2 / 3), sq_nonneg (y - 2 / 3), sq_nonneg ((3 - x - y) - 2 / 3),
          mul_pos hx hy, mul_pos hx (show (0 : ℝ) < 3 - x - y by nlinarith), mul_pos hy (show (0 : ℝ) < 3 - x - y by nlinarith), 
          sq_nonneg (x + y - (3 - x - y)), sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg ((3 - x - y) - 1)]