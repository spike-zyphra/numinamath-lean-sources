import Mathlib.Data.Real.Basic
import Mathlib.Tactic

theorem inequalities_122693
    (a b c : ℝ)
    (h₀ : 0 < a)
    (h₁ : 0 < b)
    (h₂ : 0 < c)
    (h₃ : a * b * c ≤ a + b + c) :
    a ^ 2 + b ^ 2 + c ^ 2 ≥ (Real.sqrt 3) * a * b * c := by 
  nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), 
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
          mul_pos h₀ h₁, mul_pos h₀ h₂, mul_pos h₁ h₂, 
          sq_nonneg (a * b * c - (a + b + c)), 
          Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)
        ]