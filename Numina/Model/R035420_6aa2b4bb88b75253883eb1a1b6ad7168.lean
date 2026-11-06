import Mathlib

theorem algebra_244832 (v g h : ℝ) (h₀ : v > 0) (h₁ : g > 0) (h₂ : h > 0)
    (h₃ : 5 / v = 5 / g + 5 / h) (h₄ : 15 / v = 15 / g + 15 / h - 5) :
    v = 2 := by
  field_simp at h₃ h₄ ⊢
  nlinarith [mul_pos h₀ h₁, mul_pos h₀ h₂, mul_pos h₁ h₂, mul_pos h₀ (show 0 < g * h by nlinarith), mul_pos h₁ (show 0 < h * v by nlinarith)]