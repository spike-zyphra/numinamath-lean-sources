import Mathlib

theorem algebra_20509 (s d : ℝ) (h₁ : 4 * s = 32) (h₂ : d = s * Real.pi) :
    d = 8 * Real.pi := by 
  have hs : s = 8 := by 
    linarith 
  rw [hs] at h₂
  linarith