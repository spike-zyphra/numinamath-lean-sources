import Mathlib

theorem algebra_251459 (a b c : ℝ) (h₀ : a * (-0.8)^2 + b * (-0.8) + c = 4.132)
    (h₁ : a * 1.2^2 + b * 1.2 + c = -1.948) (h₂ : a * 2.8^2 + b * 2.8 + c = -3.932)
    (h₃ : a * 1.8^2 + b * 1.8 + c = y) : y = -2.992 := by
  ring_nf at h₀ h₁ h₂ h₃
  linarith