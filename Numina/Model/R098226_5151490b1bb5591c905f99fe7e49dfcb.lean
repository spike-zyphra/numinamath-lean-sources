import Mathlib

theorem algebra_281802 (a b c : ℝ) (h₀ : a + b = 12) (h₁ : a + c = 13)
    (h₂ : b + c = 15) :
    min (min a b) c = 5 := by
  have h3 : c = b + 1 := by
    linarith
  have h4 : b = 7 := by
    linarith [h₂, h3]
  have h5 : c = 8 := by 
    rw [h4] at h3
    linarith
  have h6 : a = 5 := by 
    linarith [h₀, h4]
  rw [h6, h4, h5]
  norm_num