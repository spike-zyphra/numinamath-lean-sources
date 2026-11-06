import Mathlib

theorem algebra_127996 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : 1 / x + 2 / y + 3 / z = 1) :
    x + y / 2 + z / 3 ≥ 9 := by
  have h1 : x + y / 2 + z / 3 ≥ 9 := by
    have h2 : y * z + 2 * x * z + 3 * x * y = x * y * z := by
      field_simp at h
      nlinarith
    nlinarith [sq_nonneg (x - 3), sq_nonneg (y - 6), sq_nonneg (z - 9),
      sq_nonneg (x * y - 9 * 2), sq_nonneg (y * z - 6 * 9), sq_nonneg (x * z - 3 * 9),
      mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]
  linarith