import Mathlib

theorem algebra_912 (a b c : ℝ) (h : ∀ x, (x^2 + 3 * x - 4) ∣ x^3 + a * x^2 + b * x + c) : 4 * a + c = 12 := by
  have h₁ := h 1
  norm_num at h₁ 
  have h₂ := h (-4)
  norm_num at h₂ 
  linarith