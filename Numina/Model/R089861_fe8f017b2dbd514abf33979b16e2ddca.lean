import Mathlib

theorem algebra_8506 {a b c : ℝ} (h₀ : a + b = 3) (h₁ : b - c = 3) (h₂ : c - a = 3) :
    a + b + c = 4.5 := by
  ring_nf at h₀ h₁ h₂ ⊢
  linarith