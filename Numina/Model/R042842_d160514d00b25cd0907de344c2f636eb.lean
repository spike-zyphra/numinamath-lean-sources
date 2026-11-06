import Mathlib


theorem algebra_132788 (a b : ℝ) (h : ∃ x : ℝ, x^4 + a * x^3 + b * x^2 + a * x + 1 = 0) :
    a^2 + b^2 ≥ 4 / 5 := by
  rcases h with ⟨x, hx⟩
  have hxne : x ≠ 0 := by
    by_contra h0
    have : x = 0 := by linarith
    rw [this] at hx
    nlinarith

  have h2 : x^2 + a * x + b + a / x + 1 / x^2 = 0 := by
    have hne : x ≠ 0 := hxne
    have h3 : x^4 + a * x^3 + b * x^2 + a * x + 1 = 0 := hx
    have h4 : x^2 + a * x + b + a / x + 1 / x^2 = 0 := by
      have h5 : x^2 + a * x + b + a / x + 1 / x^2 = (x^4 + a * x^3 + b * x^2 + a * x + 1) / x^2 := by
        field_simp [show x ≠ 0 by exact hxne]
        ring
      rw [h5]
      have h6 : (x^4 + a * x^3 + b * x^2 + a * x + 1 : ℝ) = (0 : ℝ) := by linarith [hx]
      rw [h6]
      norm_num
    assumption

  have h3 : x^2 + 1 / x^2 + a * (x + 1 / x) + b = 0 := by 
    have hne : x ≠ 0 := hxne
    field_simp [hne] at h2 ⊢
    nlinarith [h2]

  have h4 : (x + 1 / x)^2 + a * (x + 1 / x) + (b - 2) = 0 := by
    have hne : x ≠ 0 := hxne
    have h5 : x^2 + 1 / x^2 = (x + 1 / x)^2 - 2 := by
      field_simp [hne]
      ring
    have h6 : x^2 + 1 / x^2 + a * (x + 1 / x) + b = 0 := by
      linarith [h3]
    nlinarith [h5, h6]

  have h5 : (x + 1 / x) ^ 2 ≥ 4 := by
    have hne : x ≠ 0 := hxne
    have h6 : (x + 1 / x) ^ 2 - 4 ≥ 0 := by
      have h7 : (x + 1 / x) ^ 2 - 4 = (x - 1 / x) ^ 2 := by 
        field_simp [hne]
        ring
      have h8 : (x - 1 / x) ^ 2 ≥ 0 := by
        apply sq_nonneg
      linarith [h7, h8]
    linarith

  nlinarith [sq_nonneg ((x + 1 / x) + 2), sq_nonneg (a - 4 / 5 * (x + 1 / x)), sq_nonneg (b + 2 / 5), sq_nonneg ((x + 1 / x) ^ 2 - 4), sq_nonneg (a + 2 * (x + 1 / x)), sq_nonneg ((x + 1 / x) - 2)]