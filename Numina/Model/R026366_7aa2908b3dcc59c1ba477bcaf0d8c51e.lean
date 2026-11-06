import Mathlib

theorem inequalities_36648 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x * y * z = 1) :
    3 / 4 ≤ x ^ 3 / ((1 + y) * (1 + z)) + y ^ 3 / ((1 + z) * (1 + x)) +
    z ^ 3 / ((1 + x) * (1 + y)) := by
  have hx1 : 0 < (1 + y) * (1 + z) := by positivity
  have hy1 : 0 < (1 + z) * (1 + x) := by positivity
  have hz1 : 0 < (1 + x) * (1 + y) := by positivity
  have h1 : x ^ 3 / ((1 + y) * (1 + z)) + y ^ 3 / ((1 + z) * (1 + x)) +
    z ^ 3 / ((1 + x) * (1 + y)) - 3 / 4 ≥ 0 := by
    have h2 : 0 < (1 + y) * (1 + z) * (1 + x) := by positivity
    have eq : x ^ 3 / ((1 + y) * (1 + z)) + y ^ 3 / ((1 + z) * (1 + x)) +
      z ^ 3 / ((1 + x) * (1 + y)) - 3 / 4 =
        (x^3 * (1 + x) + y^3 * (1 + y) + z^3 * (1 + z) - 3 / 4 * ((1 + y) * (1 + z) * (1 + x))) / ((1 + y) * (1 + z) * (1 + x)) := by 
      field_simp
      ring
    rw [eq]
    apply div_nonneg
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1),
      h, mul_pos hx hy, mul_pos hy hz, mul_pos hx hz]
    all_goals positivity
  linarith