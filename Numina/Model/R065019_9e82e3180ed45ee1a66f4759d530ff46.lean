import Mathlib

theorem inequalities_203849 (x : ℝ) (hx : x ≠ -1 ∧ x ≠ 1) :
    x^2 + 1 / (x - 1)^2 + 1 / (x + 1)^2 ≥ 2 := by
  have hx1 : x ≠ -1 := hx.1
  have hx2 : x ≠ 1 := hx.2

  have h2 : (x - 1) ≠ 0 := by
    intro h
    apply hx2
    linarith

  have h3 : (x + 1) ≠ 0 := by
    intro h
    apply hx1
    linarith

  have h1 : x^2 + 1 / (x - 1)^2 + 1 / (x + 1)^2 - 2 ≥ 0 := by
    have h4 : (x^2 + 1 / (x - 1)^2 + 1 / (x + 1)^2 - 2) =
        (x^2 * (x - 1)^2 * (x + 1)^2 + (x + 1)^2 + (x - 1)^2 - 2 * (x - 1)^2 * (x + 1)^2) / ((x - 1)^2 * (x + 1)^2) := by
      field_simp [(show (x - 1) ≠ 0 by assumption), (show (x + 1) ≠ 0 by assumption)]
      <;> ring
    have h5 : (x^2 * (x - 1)^2 * (x + 1)^2 + (x + 1)^2 + (x - 1)^2 - 2 * (x - 1)^2 * (x + 1)^2) ≥ 0 := by
      nlinarith [sq_nonneg (x^2 - 2), sq_nonneg ((x - 1) * (x + 1)), sq_nonneg (x^2 - 1), sq_nonneg (x * x), sq_nonneg (x + 1), sq_nonneg (x - 1), sq_nonneg (x^2), sq_nonneg (x^2 - 2), sq_nonneg (x ^ 2 * x ^ 2), sq_nonneg (x^2 - x)]
    have h6 : (x^2 * (x - 1)^2 * (x + 1)^2 + (x + 1)^2 + (x - 1)^2 - 2 * (x - 1)^2 * (x + 1)^2) / ((x - 1)^2 * (x + 1)^2) ≥ 0 := by
      apply div_nonneg
      linarith
      positivity
    linarith
  linarith