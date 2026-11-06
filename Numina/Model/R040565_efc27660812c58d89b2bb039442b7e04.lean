import Mathlib

theorem algebra_4490
  (a b c : ℝ)
  (h₀ : a + b + c = 6)
  (h₁ : a^2 + b^2 + c^2 = 14)
  (h₂ : a^3 + b^3 + c^3 = 36) :
  a^4 + b^4 + c^4 = 98 := by 
  have h₃ : a * b + a * c + b * c = 11 := by
    have h3 : a * b + a * c + b * c = 11 := by
      have h : (a + b + c) ^ 2 = a^2 + b^2 + c^2 + 2 * (a * b + a * c + b * c) := by ring
      rw [h₀, h₁] at h 
      linarith
    linarith
  
  have h₄ : a * b * c = 6 := by
    have h4 : a * b * c = 6 := by
      have h3 : a^3 + b^3 + c^3 - 3 * (a * b * c) = (a + b + c) * ((a^2 + b^2 + c^2) - (a * b + a * c + b * c)) := by ring
      rw [h₀, h₁, h₃] at h3
      linarith [h₂]
    linarith
  
  have h₅ : a^4 + b^4 + c^4 = (a^2 + b^2 + c^2) ^ 2 - 2 * ((a * b) ^ 2 + (a * c) ^ 2 + (b * c) ^ 2) := by ring
  
  have h₆ : (a * b) ^ 2 + (a * c) ^ 2 + (b * c) ^ 2 = 49 := by 
    have h6 : (a * b + a * c + b * c) ^ 2 = (a * b) ^ 2 + (a * c) ^ 2 + (b * c) ^ 2 + 2 * (a * b * c) * (a + b + c) := by ring
    rw [h₃, h₄, h₀] at h6
    linarith
  
  rw [h₅, h₁, h₆]
  norm_num