import Mathlib

theorem algebra_297664 {a b c : ℝ} (h₀ : a * b * c = 1) (h₁ : a + b + c = 2) (h₂ : a^2 + b^2 + c^2 = 3) :
    1 / (a * b + c - 1) + 1 / (b * c + a - 1) + 1 / (c * a + b - 1) = -2 / 3 := by
  have h3 : a * b + b * c + c * a = 1 / 2 := by
    nlinarith 
  have h4 : a * b + c - 1 ≠ 0 := by
    by_contra h
    have h5 : c = 1 - a * b := by linarith
    rw [h5] at h₁ h₂ h₀ h3
    nlinarith [sq_nonneg (a * b - 1), sq_nonneg (a + b - 1), sq_nonneg (a - 1), sq_nonneg (b - 1)]
  have h5 : b * c + a - 1 ≠ 0 := by
    by_contra h
    have h6 : a = 1 - b * c := by linarith
    rw [h6] at h₁ h₂ h₀ h3
    nlinarith [sq_nonneg (b * c - 1), sq_nonneg (b + c - 1), sq_nonneg (b - 1), sq_nonneg (c - 1)]
  have h6 : c * a + b - 1 ≠ 0 := by
    by_contra h
    have h7 : b = 1 - c * a := by linarith
    rw [h7] at h₁ h₂ h₀ h3
    nlinarith [sq_nonneg (c * a - 1), sq_nonneg (c + a - 1), sq_nonneg (c - 1), sq_nonneg (a - 1)]
  field_simp [(show a * b + c - 1 ≠ 0 by exact h4), (show b * c + a - 1 ≠ 0 by exact h5), (show c * a + b - 1 ≠ 0 by exact h6)]
  nlinarith [sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (c * a - 1),
          h₀, h₁, h₂, sq_nonneg (a * b * c - 1), h3, sq_nonneg (a + b + c - 2)]