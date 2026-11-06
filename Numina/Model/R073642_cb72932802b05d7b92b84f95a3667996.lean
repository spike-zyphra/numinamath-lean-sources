import Mathlib

theorem inequalities_598284 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hsum : x + y + z = 1) :
    x * y * z + y * z + z * x + x * y ≤ 2 + 9 * x * y * z := by
  have h1 : z = 1 - x - y := by linarith
  rw [h1]
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - (1 - x - y)), sq_nonneg (x - (1 - x - y)), 
          mul_nonneg (show 0 ≤ x by linarith) (show 0 ≤ y by linarith), 
          mul_nonneg (show 0 ≤ x by linarith) (show 0 ≤ 1 - x - y by nlinarith), 
          mul_nonneg (show 0 ≤ y by linarith) (show 0 ≤ 1 - x - y by nlinarith)]