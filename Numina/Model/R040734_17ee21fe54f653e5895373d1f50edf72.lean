import Mathlib

theorem inequalities_155585 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    x / (x ^ 4 + y ^ 2) + y / (x ^ 2 + y ^ 4) ≤ 1 / (x * y) := by
  have hxy : 0 < x * y := mul_pos hx hy
  have hx4y2_pos : 0 < x^4 + y^2 := by positivity
  have hx2y4_pos : 0 < x^2 + y^4 := by positivity

  have h1 : x / (x ^ 4 + y ^ 2) + y / (x ^ 2 + y ^ 4) - 1 / (x * y) ≤ 0 := by
    have h1 : 0 < (x ^ 4 + y ^ 2) * (x ^ 2 + y ^ 4) * (x * y) := by positivity
    have h2 : x / (x ^ 4 + y ^ 2) + y / (x ^ 2 + y ^ 4) - 1 / (x * y) =
        (x ^ 2 * y * (x ^ 2 + y ^ 4) + x * y ^ 2 * (x ^ 4 + y ^ 2) - (x ^ 4 + y ^ 2) * (x ^ 2 + y ^ 4)) / ((x ^ 4 + y ^ 2) * (x ^ 2 + y ^ 4) * (x * y)) := by
      field_simp
      ring
    rw [h2]
    apply div_nonpos_of_nonpos_of_nonneg
    · -- Show that the numerator is non-positive
      nlinarith [sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x - y), sq_nonneg (x * y - 1), sq_nonneg (x * y - x), sq_nonneg (x * y - y), sq_nonneg (x ^ 2 - y), sq_nonneg (x - y ^ 2), sq_nonneg (x * (x - y) + y * (y - x)), sq_nonneg (x^4 - y^4), sq_nonneg (x^2 - y^2), sq_nonneg (x * y * (x * y -1)), sq_nonneg (x^2 * y - y * x^2), sq_nonneg (x^3 - y^3), sq_nonneg (x^2 * y^2 - x * y), mul_pos hx hy, mul_pos hx hx, mul_pos hy hy]
    · -- Show that the denominator is non-negative
      positivity
  linarith