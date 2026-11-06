import Mathlib

open Real
open scoped BigOperators

theorem inequalities_243550 (a b c : ℝ)
  (h₀ : a > 0) (h₁ : b > 0) (h₂ : c > 0)
  (h₃ : a^2 + b^2 = c^2) :
  (1 + c / a) * (1 + c / b) ≥ 3 + 2 * sqrt 2 := by
  have h4 : (1 + c / a) * (1 + c / b) - (3 + 2 * sqrt 2) ≥ 0 := by
    have h5 : 0 < a * b := mul_pos h₀ h₁
    have h6 : (1 + c / a) * (1 + c / b) - (3 + 2 * sqrt 2) = 
        ( (a * b + b * c + a * c + c^2) - (3 + 2 * sqrt 2) * (a * b) ) / (a * b) := by
      field_simp
      ring
    rw [h6]
    have h8 : (a * b + b * c + a * c + c^2) - (3 + 2 * sqrt 2) * (a * b) ≥ 0 := by
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (a - b), sq_nonneg (a + b - c), 
        mul_pos h₀ h₁, mul_pos h₀ h₂, mul_pos h₁ h₂, 
        sq_nonneg (c^2 - 2 * (a * b)), sq_nonneg (c - a * sqrt 2), sq_nonneg (c - b * sqrt 2), 
        sq_nonneg (a * b), h₃, 
        mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 2)
      ]
    apply div_nonneg 
    linarith
    positivity
  linarith