import Mathlib

theorem inequalities_60691 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x^2 + y^2 + z^2 = 1) :
    x^2 * y * z + x * y^2 * z + x * y * z^2 ≤ 1 / 3 := by

  have h1 : x^2 * y * z + x * y^2 * z + x * y * z^2 = x * y * z * (x + y + z) := by
    ring

  have h3 : x * y * z * (x + y + z) ≤ 1 / 3 := by
    nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
              sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), 
              h, mul_pos hx hy, mul_pos hx hz, mul_pos hy hz
           ]

  rw [h1]
  linarith [h3]