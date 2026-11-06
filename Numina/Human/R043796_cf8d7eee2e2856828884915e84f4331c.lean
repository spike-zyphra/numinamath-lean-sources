import Mathlib

theorem inequalities_103104 {a b : ℝ} (h₀ : a^3 - b^3 = 2) (h₁ : a^5 - b^5 ≥ 4) :
    a^2 + b^2 ≥ 2 := by 
  have h2 : a - b ≠ 0 := by
    by_contra h
    have h3 : a^3 - b^3 = 0 := by
      have : a = b := by linarith
      rw [this]
      ring
    linarith

  have h3 : a - b > 0 := by
    by_contra h
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a^2 + b^2), sq_nonneg (a^2 - b^2),
              h₀]

  have h4 : a^5 - b^5 - 2 * (a^3 - b^3) ≥ 0 := by linarith [h₀, h₁]

  have h5 : (a - b) * (a^4 + a^3 * b + a^2 * b^2 + a * b^3 + b^4 - 2 * (a^2 + a * b + b^2)) ≥ 0 := by
    have h6 : a^5 - b^5 - 2 * (a^3 - b^3) = (a - b) * (a^4 + a^3 * b + a^2 * b^2 + a * b^3 + b^4 - 2 * (a^2 + a * b + b^2)) := by
      ring
    linarith [h4, h6]

  have h7 : a^4 + a^3 * b + a^2 * b^2 + a * b^3 + b^4 - 2 * (a^2 + a * b + b^2) ≥ 0 := by
    nlinarith [h3, h5]

  have h8 : a^2 + b^2 + a * b > 0 := by
    have h9 : a^3 - b^3 = 2 := h₀
    have h10 : a - b > 0 := h3
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), h₀, h3]
  
  have h9 : (a^2 + b^2 - 2) * (a^2 + b^2 + a * b) ≥ 0 := by
    nlinarith [h7]

  have h10 : a^2 + b^2 - 2 ≥ 0 := by
    nlinarith [h8, h9]

  linarith [h10]