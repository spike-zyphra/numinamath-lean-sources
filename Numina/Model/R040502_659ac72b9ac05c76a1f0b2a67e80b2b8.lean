import Mathlib

theorem inequalities_184398 (x y : ℝ) (hx : x < 0) (hy : y < 0) :
    (x ^ 4 / y ^ 4 + y ^ 4 / x ^ 4 - x ^ 2 / y ^ 2 - y ^ 2 / x ^ 2 + x / y + y / x ≥ 2) := by

  have h3 : x ≠ 0 := by linarith
  have h4 : y ≠ 0 := by linarith

  have h5 : x ^ 4 / y ^ 4 + y ^ 4 / x ^ 4 - x ^ 2 / y ^ 2 - y ^ 2 / x ^ 2 + x / y + y / x - 2 ≥ 0 := by
    have h6 : 0 < x ^ 4 * y ^ 4 := by positivity
    have hx1 : x ^ 4 / y ^ 4 + y ^ 4 / x ^ 4 - x ^ 2 / y ^ 2 - y ^ 2 / x ^ 2 + x / y + y / x - 2 =
        (x ^ 8 + y ^ 8 - x ^ 6 * y ^ 2 - y ^ 6 * x ^ 2 + x ^ 5 * y ^ 3 + x ^ 3 * y ^ 5 - 2 * x ^ 4 * y ^ 4) / (x ^ 4 * y ^ 4) := by
      field_simp [h3, h4]
      ring
    rw [hx1] at *
    apply div_nonneg
    · -- Prove the numerator ≥0
      have h8 : x ^ 2 > 0 := by nlinarith
      have h9 : y ^ 2 > 0 := by nlinarith
      have h10 : x * y > 0 := by nlinarith
      nlinarith [sq_nonneg (x^4 - y^4), sq_nonneg (x^2 - y^2), sq_nonneg (x^2 * y^2), sq_nonneg (x * y - 1), sq_nonneg (x^2 - y^2), sq_nonneg (x^3 - y^3), sq_nonneg (x * y), sq_nonneg (x^2 * y^2 - x * y), sq_nonneg (x^4 - x^2 * y^2), sq_nonneg (y^4 - x^2 * y^2), sq_nonneg (x^4 - y^4), sq_nonneg (x^2 * y^2 - x^2), sq_nonneg (x^2 * y^2 - y^2), mul_pos (show 0 < x ^ 2 by nlinarith) (show 0 < y ^ 2 by nlinarith), sq_nonneg (x^2 - y^2), sq_nonneg (x + y), sq_nonneg (x * y), sq_nonneg (x^2 * y^2 - x ^ 2 * y), sq_nonneg (x^2 - y^2), sq_nonneg (x^4 - y^4)]
    · -- Prove the denominator >0
      positivity

  linarith