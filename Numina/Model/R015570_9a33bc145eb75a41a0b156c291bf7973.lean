import Mathlib

open BigOperators Real

theorem inequalities_237752 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
  (h : x + y > z) (h' : y + z > x) (h'' : z + x > y) :
  (x + y + z) * (x + y - z) * (x + z - y) * (z + y - x) ≤ 4 * x^2 * y^2 := by

  have h1 : 0 < x + y - z := by linarith
  have h2 : 0 < y + z - x := by linarith
  have h3 : 0 < z + x - y := by linarith

  nlinarith [sq_nonneg (x ^ 2 + y ^ 2 - z ^ 2), sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
          sq_nonneg (x + y - z), sq_nonneg (y + z - x), sq_nonneg (z + x - y),
          mul_pos hx hy, mul_pos hx hz, mul_pos hy hz,
          mul_pos h1 h2, mul_pos h1 h3, mul_pos h2 h3]