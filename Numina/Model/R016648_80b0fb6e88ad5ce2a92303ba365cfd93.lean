import Mathlib

theorem algebra_297531 {a b : ℝ} (h : ∀ x : ℝ, (x^3 - a * x^2 - 1003 * x + b) % (x^2 - 999 * x + 1994) = 0) :
    b - 6 * a = 6 := by
  have h₁ := h 2
  have h₂ := h 997
  norm_num at h₁ h₂ 
  nlinarith