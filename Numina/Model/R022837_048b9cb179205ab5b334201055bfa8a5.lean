import Mathlib

theorem algebra_181991 {a b c : ℝ} (h₀ : a + b + c = 5) (h₁ : a ^ 2 + b ^ 2 + c ^ 2 = 15)
    (h₂ : a ^ 3 + b ^ 3 + c ^ 3 = 47) :
    (a ^ 2 + a * b + b ^ 2) * (b ^ 2 + b * c + c ^ 2) * (c ^ 2 + c * a + a ^ 2) = 625 := by 
  have h₃ : a * b + a * c + b * c = 5 := by
    have eq1 : a ^ 2 + b ^ 2 + c ^ 2 = (a + b + c) ^ 2 - 2 * (a * b + a * c + b * c) := by
      ring
    rw [h₀] at eq1
    linarith

  have h₄ : a * b * c = -1 := by
    have eq1 : a ^ 3 + b ^ 3 + c ^ 3 - 3 * (a * b * c) = (a + b + c) * ((a ^ 2 + b ^ 2 + c ^ 2) - (a * b + a * c + b * c)) := by
      ring
    rw [h₀, h₁, h₃] at eq1
    linarith

  nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), sq_nonneg (a + b + c - 5), sq_nonneg (a * b + a * c + b * c - 5), sq_nonneg (a * b * c + 1)]