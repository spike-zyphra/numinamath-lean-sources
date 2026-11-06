import Mathlib

theorem algebra_259078 (c s t : ℝ) (h₀ : c = 5) (h₁ : s = 3 * c) (h₂ : t = 5 * c) :
    c + s + t = 45 := by
  rw [h₀] at h₁ h₂
  rw [h₁, h₂, h₀]
  norm_num