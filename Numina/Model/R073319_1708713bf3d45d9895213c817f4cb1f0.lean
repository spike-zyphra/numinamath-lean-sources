import Mathlib

theorem algebra_231233 (a b c : ℝ) (h₀ : 2*a+3*b+2*c=75) (h₁ : 2*a+3*c+2*b=88)
    (h₂ : b=c+6) :
    b-a=1 := by
  rw [h₂] at h₀ h₁
  linarith