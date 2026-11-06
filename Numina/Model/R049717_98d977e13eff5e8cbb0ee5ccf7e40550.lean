import Mathlib

theorem algebra_237036 (a b c : ℝ) (h₀ : a + b + c = 0) (h₁ : a^2 + b^2 + c^2 = 6) :
    a^4 + b^4 + c^4 = 18 := by
  have h₂ : a * b + a * c + b * c = -3 := by
    have h : (a + b + c)^2 = a^2 + b^2 + c^2 + 2 * (a * b + a * c + b * c) := by ring
    rw [h₀, h₁] at h
    linarith

  have h₃ : a^4 + b^4 + c^4 = (a^2 + b^2 + c^2)^2 - 2 * ((a * b)^2 + (a * c)^2 + (b * c)^2) := by ring
  
  have h₄ : (a * b)^2 + (a * c)^2 + (b * c)^2 = 9 := by
    have h : (a * b + a * c + b * c)^2 = (a * b)^2 + (a * c)^2 + (b * c)^2 + 2 * (a * b * c) * (a + b + c) := by ring
    rw [h₂, h₀] at h
    linarith
  
  rw [h₃]
  rw [h₁]
  rw [h₄]
  norm_num