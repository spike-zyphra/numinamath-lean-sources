import Mathlib

theorem inequalities_100649 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hsum : x + y + z = 1) :
    (1 - x) * (1 - y) * (1 - z) ≥ 8 * x * y * z := by
  have h1 : z = 1 - x - y := by linarith
  rw [h1]
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - (1 - x - y)), sq_nonneg (x - (1 - x - y)), 
          mul_pos hx hy, mul_pos hx (show 0 < 1 - x - y by nlinarith), mul_pos hy (show 0 < 1 - x - y by nlinarith), 
          sq_nonneg (x + y - (1 - x - y)), 
          sq_nonneg (x - y), sq_nonneg (x - (1 - x - y)), sq_nonneg (y - (1 - x - y))]