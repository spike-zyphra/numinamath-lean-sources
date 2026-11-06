import Mathlib

theorem algebra_194665 (d v1 v2 : ℝ) (h₀ : d > 0) (h₁ : v1 > 0) (h₂ : v2 > 0)
    (h₃ : d / v1 = 2) (h₄ : d / v2 = 30 / 60) (h₅ : d / v2 = d / v1 - 30 / 60) :
    v1 = 56 := by 
  field_simp at h₃ h₄ h₅
  nlinarith