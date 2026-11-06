import Mathlib

open Real
open scoped BigOperators

theorem inequalities_88015 (a b c : ℝ) (h₀ : a > 0) (h₁ : b > 0) (h₂ : c > 0)
  (h₃ : a^2 = b^2 + c^2) :
  (a + b + c) * (1 / a + 1 / b + 1 / c) ≥ 5 + 3 * sqrt 2 := by
  have h4 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    all_goals linarith

  have h5 : (a + b + c) * (1 / a + 1 / b + 1 / c) - (5 + 3 * Real.sqrt 2) ≥ 0 := by
    have h11 : 0 < a * b * c := h4
    have h12 : (a + b + c) * (1 / a + 1 / b + 1 / c) - (5 + 3 * Real.sqrt 2) =
        ( (a + b + c) * (a * b + b * c + c * a) - (5 + 3 * Real.sqrt 2) * (a * b * c) ) / (a * b * c) := by
      field_simp
      ring
    rw [h12] at *
    apply div_nonneg
    · -- Numerator ≥ 0
      have h13 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
      have h14 : Real.sqrt 2 ≥ 0 := Real.sqrt_nonneg 2
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
        sq_nonneg (a^2 - 2 * (b * c)), sq_nonneg ( (b + c) ^ 2 - 2 * (b * c) ), 
        sq_nonneg ( (b * c) - a^2 / 2 ), sq_nonneg ( (b + c) - a ), sq_nonneg ( (b + c) * a - 2 * (b * c) * Real.sqrt 2 ), 
        sq_nonneg (b * c - a^2), sq_nonneg ( (b * c) - ( (b + c) ^ 2 ) * Real.sqrt 2 / 2 ), 
        mul_pos h₀ h₁, mul_pos h₀ h₂, mul_pos h₁ h₂, 
        sq_nonneg (b * c), sq_nonneg ( (b - c) ), sq_nonneg ( (b + c) ^ 2 - 2 * (b * c) ), 
        mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 2), 
        Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), 
        sq_nonneg (a^2 - 2), sq_nonneg ( (b * c) ^ 2 - ( (b + c) ^ 2 * a^2 * Real.sqrt 2 / 2 ) ) 
      ]
    all_goals positivity
  linarith