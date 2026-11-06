import Mathlib

theorem inequalities_8995 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hxyz : x * y * z = 1) :
    3 / 4 ≤ x^3 / ((1 + y) * (1 + z)) + y^3 / ((1 + x) * (1 + z)) + z^3 / ((1 + x) * (1 + y)) := by

  have hx1 : 0 < (1 + y) * (1 + z) := by positivity
  have hy1 : 0 < (1 + x) * (1 + z) := by positivity
  have hz1 : 0 < (1 + x) * (1 + y) := by positivity

  have h1 : x^3 / ((1 + y) * (1 + z)) + y^3 / ((1 + x) * (1 + z)) + z^3 / ((1 + x) * (1 + y)) - 3 / 4 ≥ 0 := by
    have hx2 : 0 < (1 + x) * (1 + y) * (1 + z) := by positivity
    have h2 : x^3 / ((1 + y) * (1 + z)) + y^3 / ((1 + x) * (1 + z)) + z^3 / ((1 + x) * (1 + y)) - 3 / 4 =
        (4 * x^3 * (1 + x) + 4 * y^3 * (1 + y) + 4 * z^3 * (1 + z) - 3 * (1 + x) * (1 + y) * (1 + z)) / (4 * (1 + x) * (1 + y) * (1 + z)) := by
      field_simp
      ring
    rw [h2] at *
    apply div_nonneg
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1),
      hxyz, mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]
    positivity

  linarith [h1]