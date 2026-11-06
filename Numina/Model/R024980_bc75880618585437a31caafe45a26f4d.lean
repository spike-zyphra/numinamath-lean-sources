import Mathlib

theorem algebra_196375 (a b : ℝ) (h : ∃ x : ℝ, x^4 + a * x^3 + b * x^2 + a * x + 1 = 0) :
    a^2 + b^2 ≥ 4 / 5 := by
  rcases h with ⟨x, hx⟩
  have h1 : x ≠ 0 := by
    by_contra h1
    rw [h1] at hx
    nlinarith
  have eq1 : x^2 + a * x + b + a / x + 1 / x^2 = 0 := by
    have h3 : x^4 + a * x^3 + b * x^2 + a * x + 1 = 0 := hx
    have h4 : x^4 + a * x^3 + b * x^2 + a * x + 1 = (x^2 + a * x + b + a / x + 1 / x^2) * x^2 := by
      field_simp
      ring
    rw [h4] at h3
    have h5 : x^2 ≠ 0 := by
      exact pow_ne_zero 2 h1
    have eq3 : x^2 + a * x + b + a / x + 1 / x^2 = 0 := by
      apply (mul_eq_zero.mp h3).resolve_right
      exact h5
    linarith
  have eq2 : (x + 1 / x)^2 + a * (x + 1 / x) + (b - 2) = 0 := by
    have eq3 : x^2 + a * x + b + a / x + 1 / x^2 = 0 := eq1
    have eq4 : x^2 + a * x + b + a / x + 1 / x^2 = (x + 1 / x)^2 + a * (x + 1 / x) + (b - 2) := by
      field_simp
      ring
    rw [eq4] at eq3
    linarith
  have h3 : (x + 1 / x)^2 ≥ 4 := by
    have h4 : (x + 1 / x)^2 - 4 ≥ 0 := by
      have h5 : (x + 1 / x)^2 - 4 = (x - 1 / x)^2 := by
        field_simp
        <;> nlinarith
      have h6 : (x - 1 / x)^2 ≥ 0 := sq_nonneg (x - 1 / x)
      linarith
    linarith
  nlinarith [sq_nonneg (a + 4 / 5), sq_nonneg (b + 2 / 5), sq_nonneg ((x + 1 / x) + 2), sq_nonneg ((x + 1 / x) - 2), sq_nonneg (a + b), sq_nonneg (a - b)]