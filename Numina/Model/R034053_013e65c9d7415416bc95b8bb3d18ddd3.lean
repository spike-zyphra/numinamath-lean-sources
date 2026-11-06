import Mathlib

theorem inequalities_213948 (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) :
    x^4 + y^4 + 2 / (x^2 * y^2) ≥ 4 := by
  have h1 : x^2 > 0 := by
    exact sq_pos_of_ne_zero hx
  have h2 : y^2 > 0 := by
    exact sq_pos_of_ne_zero hy
  have h3 : x^2 * y^2 > 0 := by
    apply mul_pos
    exact sq_pos_of_ne_zero hx
    exact sq_pos_of_ne_zero hy
  have h4 : x ^ 4 + y ^ 4 + 2 / (x^2 * y^2) - 4 ≥ 0 := by
    have pos1 : x^2 * y^2 > 0 := h3
    have h5 : (x ^ 4 + y ^ 4 + 2 / (x^2 * y^2) - 4) = (x ^ 6 * y ^ 2 + x ^ 2 * y ^ 6 + 2 - 4 * (x^2 * y^2)) / (x^2 * y^2) := by
      field_simp
      ring
    rw [h5] at *
    apply div_nonneg
    -- Prove the numerator is non-negative
    nlinarith [sq_nonneg (x ^ 2 * y ^ 2 - 1), sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x^3 * y - x * y^3), sq_nonneg (x^2 * y^2), sq_nonneg (x^2 - 1), sq_nonneg (y^2 - 1), sq_nonneg (x * y), sq_nonneg (x^2 * y - y), sq_nonneg (x * y^2 - x), sq_nonneg (x^2 * y^2 - 1), pow_two_nonneg (x^2 - y^2), pow_two_nonneg (x^2 * y - x * y^2)]
    -- Prove the denominator is positive
    positivity
  linarith