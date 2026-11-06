import Mathlib

theorem inequalities_598801
    (a b c : ℝ)
    (h₀ : 0 < a)
    (h₁ : 0 < b)
    (h₂ : 0 < c)
    (h₃ : a * b + b * c + c * a + 2 * a * b * c = 1) :
    2 * (a + b + c) + 1 ≥ 32 * a * b * c := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
            sq_nonneg (a * b - a * c), sq_nonneg (a * b - b * c), sq_nonneg (a * c - b * c), 
            mul_pos h₀ h₁, mul_pos h₀ h₂, mul_pos h₁ h₂, 
            sq_nonneg (a + b + c - 3 / 2), 
            mul_pos (show 0 < a * b by nlinarith) (show 0 < c by linarith)]