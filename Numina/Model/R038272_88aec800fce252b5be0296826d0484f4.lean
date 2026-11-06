import Mathlib

theorem inequalities_215966 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    (x + 8 * y + 2 * z) * (x + 2 * y + z) * (x + 4 * y + 4 * z) ≥ 256 * x * y * z := by
  have h1 : 0 < x + 8 * y + 2 * z := by
    linarith
  have h2 : 0 < x + 2 * y + z := by
    linarith
  have h3 : 0 < x + 4 * y + 4 * z := by
    linarith
  nlinarith [sq_nonneg (x - 4 * y), sq_nonneg (x - 2 * z), sq_nonneg (z - 2 * y), 
    sq_nonneg (x - 4 * y - 2 * z), sq_nonneg (x - 2 * y + z), sq_nonneg (x + 2 * y - z), sq_nonneg (z - 2 * y),
    mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, 
    mul_pos (show 0 < x by linarith) (show 0 < y by linarith), 
    mul_pos (show 0 < x by linarith) (show 0 < z by linarith), 
    mul_pos (show 0 < y by linarith) (show 0 < z by linarith)]