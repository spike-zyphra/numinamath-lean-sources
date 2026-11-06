import Mathlib

theorem algebra_194518 (x : ℝ) (h : 183 * x = 1) (h' : 37 * 5 * x = 1) :
    1 / x = 365 := by
  exfalso
  have h₁ : 183 * x = 1 := h
  have h₂ : 185 * x = 1 := by
    nlinarith 
  have h₃ : 183 * x = 185 * x := by 
    linarith [h₁, h₂]
  have h₄ : x = 0 := by 
    nlinarith 
  rw [h₄] at h₁
  norm_num at h₁