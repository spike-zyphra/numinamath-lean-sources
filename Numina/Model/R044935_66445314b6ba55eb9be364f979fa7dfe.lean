import Mathlib

theorem inequalities_282331 (a b : ℝ) (h₀ : a ≠ 0) (h₁ : b ≠ 0)
    (h₂ : a + b > 0) :
    a / b^2 + b / a^2 ≥ 1 / a + 1 / b := by
  have h3 : a / b^2 + b / a^2 - (1 / a + 1 / b) ≥ 0 := by
    have h4 : a / b^2 + b / a^2 - (1 / a + 1 / b) =
        ( (a - b)^2 * (a + b) ) / (a^2 * b^2) := by
      field_simp
      ring
    rw [h4]
    apply div_nonneg
    -- Show numerator is non-negative
    have h5 : (a - b) ^ 2 ≥ 0 := by
      apply sq_nonneg
    have h6 : (a - b)^2 * (a + b) ≥ 0 := by
      have h7 : a + b > 0 := h₂
      nlinarith [h5, h7]
    linarith
    -- Show denominator is positive
    positivity
  linarith [h3]