import Mathlib

theorem inequalities_126420 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxyz : x * y * z = 1) :
    3 / 4 ≤ x ^ 3 / ((1 + y) * (1 + z)) + y ^ 3 / ((1 + z) * (1 + x)) +
    z ^ 3 / ((1 + x) * (1 + y)) := by
  have h1 : 0 < x * y * z := by
    apply mul_pos
    apply mul_pos
    all_goals linarith
  have h2 : 0 < (1 + x) * (1 + y) * (1 + z) := by
    apply mul_pos
    apply mul_pos
    all_goals
      nlinarith
  have h3 : x ^ 3 / ((1 + y) * (1 + z)) + y ^ 3 / ((1 + z) * (1 + x)) + z ^ 3 / ((1 + x) * (1 + y)) - 3 / 4 ≥ 0 := by
    have h4 : x ^ 3 / ((1 + y) * (1 + z)) + y ^ 3 / ((1 + z) * (1 + x)) + z ^ 3 / ((1 + x) * (1 + y)) - 3 / 4 =
        (x ^ 3 * (1 + x) + y ^ 3 * (1 + y) + z ^ 3 * (1 + z) - 3 / 4 * ((1 + x) * (1 + y) * (1 + z))) / ((1 + x) * (1 + y) * (1 + z)) := by
      field_simp
      ring
    rw [h4]
    have h5 : 0 < (1 + x) * (1 + y) * (1 + z) := h2
    apply div_nonneg
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1),
      hxyz, mul_pos hx hy, mul_pos hy hz, mul_pos hz hx, mul_pos hx hz, mul_pos hy hx]
    positivity
  linarith