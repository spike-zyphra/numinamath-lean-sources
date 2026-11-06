import Mathlib

theorem inequalities_598523 (x1 x2 x3 : ℝ) (hx1 : 0 < x1) (hx2 : 0 < x2) (hx3 : 0 < x3) :
    x2 / x1 + x3 / x2 + x1 / x3 ≤ (x1 / x2) ^ 2 + (x2 / x3) ^ 2 + (x3 / x1) ^ 2 := by
  have h1 : 0 < x1 * x2 * x3 := by
    apply mul_pos
    apply mul_pos
    exact hx1
    exact hx2
    exact hx3
  have eq1 : x2 / x1 + x3 / x2 + x1 / x3 - ((x1 / x2) ^ 2 + (x2 / x3) ^ 2 + (x3 / x1) ^ 2) ≤ 0 := by
    have commonDenominator : 0 < x1^2 * x2^2 * x3^2 := by positivity
    have eq2 : x2 / x1 + x3 / x2 + x1 / x3 - ((x1 / x2) ^ 2 + (x2 / x3) ^ 2 + (x3 / x1) ^ 2) =
        (x2^3 * x1 * x3^2 + x3^3 * x1^2 * x2 + x1^3 * x2^2 * x3 - (x1^4 * x3^2 + x1^2 * x2^4 + x2^2 * x3^4)) / (x1^2 * x2^2 * x3^2) := by
      field_simp
      ring
    rw [eq2]
    apply div_nonpos_of_nonpos_of_nonneg
    nlinarith [sq_nonneg (x1^2 * x3 - x2^2 * x1), sq_nonneg (x2^2 * x3 - x1 * x3^2), sq_nonneg (x3^2 * x1 - x1 * x2^2), 
          sq_nonneg (x1 * x3 - x2^2), sq_nonneg (x2 * x3 - x1^2), sq_nonneg (x1 * x2 - x3^2), 
          sq_nonneg (x1^2 * x2 - x1^2 * x3), sq_nonneg (x1^2 * x2 - x2^2 * x3), sq_nonneg (x1^2 * x3 - x2^2 * x3),
          mul_pos hx1 hx2, mul_pos hx1 hx3, mul_pos hx2 hx3]
    positivity
  linarith