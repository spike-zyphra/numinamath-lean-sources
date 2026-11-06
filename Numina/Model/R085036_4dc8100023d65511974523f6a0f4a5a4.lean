import Mathlib

open Real

theorem algebra_311107 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x * y + z = (x + z) * (y + z)) :
    x * y * z ≤ 1 / 27 := by
  have h1 : x + y + z = 1 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (x - z), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]
  have h2 : x * y * z ≤ ( (x + y + z) / 3 ) ^ 3 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (x - z), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]
  rw [h1] at h2
  have h3 : x * y * z ≤ (1 / 27 : ℝ) := by
    nlinarith [h2]
  linarith