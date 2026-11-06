import Mathlib

theorem algebra_326037 {a b c : ℝ} (h₀ : a > 0) (h₁ : b > 0) (h₂ : c > 0)
    (h₃ : a^2 + b^2 = c^2) (h₄ : a < b) (h₅ : b < c) (h₆ : b / (c + a) + a / (c + b) = 13 / 15) :
    a / b = 5 / 12 := by
  have h7 : c + a > 0 := by
    linarith
  have h8 : c + b > 0 := by
    linarith
  have h9 : b * 15 * (c + b) + a * 15 * (c + a) = 13 * (c + a) * (c + b) := by
    field_simp [(show c + a ≠ 0 by linarith), (show c + b ≠ 0 by linarith)] at h₆ ⊢
    nlinarith [h₆]
  -- Solving these equations
  have h10 : 2 * a^2 + 2 * b^2 - 13 * a * b + 2 * c * (a + b) = 0 := by
    nlinarith
  have h11 : a / b = 5 / 12 := by
    have h12 : (a) ^ 2 + (b) ^ 2 = c ^ 2 := h₃
    have h14 : (a - 5 * b / 12) * (a - 12 * b / 5) = 0 := by
      nlinarith [sq_nonneg (a - 5 * b / 12), sq_nonneg (b - 12 * a / 5), sq_nonneg (c - 13 * b / 12), sq_nonneg (c - 13 * a / 5), mul_pos h₀ h₁, mul_pos h₀ h₂, mul_pos h₁ h₂]
    cases' (mul_eq_zero.1 h14) with h15 h16
    · -- Case 1: a - 5 * b / 12 = 0
      have h17 : a / b = 5 / 12 := by
        have h18 : a = 5 * b / 12 := by
          linarith
        have h19 : b ≠ 0 := by
          linarith
        field_simp [h19]
        nlinarith
      linarith
    · -- Case 2: a - 12 * b / 5 = 0
      have h18 : a > b := by
        have h17 : a = 12 * b / 5 := by
          linarith
        nlinarith
      linarith
  exact h11