import Mathlib

theorem inequalities_601946 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (h : x + y + z = 1) :
    x * y + y * z + z * x - 2 * x * y * z ≤ 7 / 27 := by
  have h1 : z = 1 - x - y := by linarith
  rw [h1]
  nlinarith [sq_nonneg (x - y), sq_nonneg (x - (1 - x - y)), sq_nonneg (y - (1 - x - y)), 
          mul_nonneg hx hy, 
          mul_nonneg hy (show 0 ≤ 1 - x - y by nlinarith), 
          mul_nonneg (show 0 ≤ 1 - x - y by nlinarith) hx, 
          sq_nonneg (x + y - (1 - x - y)), 
          sq_nonneg (x - 2 / 3), sq_nonneg (y - 2 / 3), 
          sq_nonneg ((1 - x - y) - 2 / 3), 
          sq_nonneg (x - y), 
          sq_nonneg (x - (1 - x - y)), 
          sq_nonneg (y - (1 - x - y)), 
          mul_nonneg (show 0 ≤ x by linarith) (show 0 ≤ 1 - x - y by linarith), 
          mul_nonneg (show 0 ≤ y by linarith) (show 0 ≤ 1 - x - y by linarith), 
          sq_nonneg (x + y - 2 / 3), sq_nonneg ((1 - x - y) - 2 / 3), 
          sq_nonneg (x + y - (1 - x - y))]