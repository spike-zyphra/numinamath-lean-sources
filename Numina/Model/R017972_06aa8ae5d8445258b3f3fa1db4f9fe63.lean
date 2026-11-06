import Mathlib

theorem inequalities_599901 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hsum : x + y + z = 1) :
    x ^ 2 + y ^ 2 + z ^ 2 + 9 * x * y * z ≥ 2 * (x * y + y * z + z * x) := by
  have h1 : z = 1 - x - y := by linarith
  rw [h1]
  nlinarith [sq_nonneg (x - y), sq_nonneg ((1 - x - y) - x), sq_nonneg ((1 - x - y) - y), sq_nonneg (x + y - (1 - x - y)), mul_pos hx hy, mul_pos hx (show 0 < 1 - x - y by nlinarith), mul_pos hy (show 0 < 1 - x - y by nlinarith)]