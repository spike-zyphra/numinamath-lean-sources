import Mathlib

theorem inequalities_598090 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x * y + y * z + z * x = 1) :
    (x + y) * (y + z) * (z + x) ≥ 8 / 9 * (x + y + z) := by
  nlinarith [sq_nonneg (x + y + z - 1), sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
    sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
    mul_nonneg (show 0 ≤ x by linarith) (show 0 ≤ y by linarith), 
    mul_nonneg (show 0 ≤ y by linarith) (show 0 ≤ z by linarith), 
    mul_nonneg (show 0 ≤ z by linarith) (show 0 ≤ x by linarith),
    mul_pos hx hy, mul_pos hx hz, mul_pos hy hz
  ]