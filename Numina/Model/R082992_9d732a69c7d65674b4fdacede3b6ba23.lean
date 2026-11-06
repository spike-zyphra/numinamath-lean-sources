import Mathlib

theorem algebra_285255 (v o : ℝ) (h₀ : v > 0) (h₁ : o > 0)
    (h₂ : 11 / v = 2) (h₃ : 8 / (v + o) = 3) :
    8 / o = 1.5 := by 
  have h4 : v = 11 / 2 := by 
    field_simp at h₂
    linarith 
  have h5 : v + o = 8 / 3 := by 
    field_simp at h₃
    nlinarith

  rw [h4] at h5 
  linarith