import Mathlib

theorem algebra_600003 (a b : ℝ) (h : ∃ x : ℝ, x^4 + a * x^3 + b * x^2 + a * x + 1 = 0) :
    a^2 + b^2 ≥ 4 / 5 := by
  rcases h with ⟨x, hx⟩
  have h1 : x ≠ 0 := by
    by_contra h1
    rw [h1] at hx
    nlinarith
  have h2 : x^4 + a * x^3 + b * x^2 + a * x + 1 = 0 := hx
  have h3 : x^2 + a * x + b + a / x + 1 / x^2 = 0 := by
    have h4 : x ≠ 0 := h1
    have h5 : x^4 + a * x^3 + b * x^2 + a * x + 1 = 0 := hx
    have h6 : x^2 + a * x + b + a / x + 1 / x^2 = (x^4 + a * x^3 + b * x^2 + a * x + 1) / x^2 := by
      field_simp
      ring
    rw [h6]
    rw [h5]
    norm_num
  have h4 : (x + 1 / x) ^ 2 + a * (x + 1 / x) + (b - 2) = 0 := by
    have h7 : x^2 + a * x + b + a / x + 1 / x^2 = 0 := h3
    have h8 : x^2 + a * x + b + a / x + 1 / x^2 = (x + 1 / x) ^ 2 + a * (x + 1 / x) + (b - 2) := by
      field_simp
      ring
    linarith [h7, h8]
  have h5 : (x + 1 / x) ^ 2 ≥ 4 := by
    have h10 : x ≠ 0 := h1
    have h7 : (x + 1 / x) ^ 2 ≥ 4 := by
      have h8 : (x + 1 / x) ^ 2 - 4 ≥ 0 := by
        have h9 : (x + 1 / x) ^ 2 - 4 = (x - 1 / x) ^ 2 := by
          field_simp
          ring
        have h10 : (x - 1 / x) ^ 2 ≥ 0 := by
          apply sq_nonneg
        linarith [h9, h10]
      linarith
    linarith
  nlinarith [sq_nonneg ((x + 1 / x) + 2), sq_nonneg (a - (4 / 5) * (x + 1 / x)), sq_nonneg (b + 2 / 5), sq_nonneg (a + 4 / 5), sq_nonneg ((x + 1 / x) ^ 2 - 4), sq_nonneg ((x + 1 / x) + 2 * a), sq_nonneg ((x + 1 / x) ^ 2 + a * (x + 1 / x) - 1), sq_nonneg (a - 4 / 5), sq_nonneg (b + 2 / 5), sq_nonneg (a + 4 / 5), sq_nonneg ((x + 1 / x) - 2), sq_nonneg ((x + 1 / x) + 2)]