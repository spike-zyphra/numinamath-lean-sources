import Mathlib

theorem algebra_2780 (a b c : ℝ) (h₀ : a + b + c = 5) (h₁ : a ^ 2 + b ^ 2 + c ^ 2 = 15) (h₂ : a ^ 3 + b ^ 3 + c ^ 3 = 47) :
    (a ^ 2 + a * b + b ^ 2) * (b ^ 2 + b * c + c ^ 2) * (c ^ 2 + c * a + a ^ 2) = 625 := by
  have h₃ : a * b + a * c + b * c = 5 := by
    have eq1 : (a + b + c) ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 + 2 * (a * b + a * c + b * c) := by
      ring
    rw [h₀, h₁] at eq1
    linarith
  have h₄ : a * b * c = -1 := by
    have eq1 : a ^ 3 + b ^ 3 + c ^ 3 - 3 * (a * b * c) = (a + b + c) * ( (a ^ 2 + b ^ 2 + c ^ 2) - (a * b + a * c + b * c) ) := by 
      ring
    rw [h₀, h₁, h₃, h₂] at eq1
    linarith
  nlinarith [sq_nonneg (a * b - a * c), sq_nonneg (a * b - b * c), sq_nonneg (a * c - b * c), sq_nonneg (a + b + c - 5), sq_nonneg (a * b * c + 1), h₃, h₄, sq_nonneg (a * b + a * c + b * c - 5)]