import Mathlib

theorem inequalities_601247 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x + y + z ≥ x * y * z) :
    x ^ 2 * y ^ 2 * z ^ 2 ≤ x ^ 4 + y ^ 4 + z ^ 4 := by
  have h1 : x * y > 0 := by
    positivity
  have h2 : x * y * z > 0 := by
    positivity
  nlinarith [sq_nonneg (x^2 - y^2), sq_nonneg (y^2 - z^2), sq_nonneg (z^2 - x^2),
          sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
          mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, 
          sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y), 
          mul_pos (show 0 < x by linarith) (show 0 < y by linarith), 
          mul_pos (show 0 < y by linarith) (show 0 < z by linarith), 
          mul_pos (show 0 < z by linarith) (show 0 < x by linarith)]