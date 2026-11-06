import Mathlib

open Real
open scoped BigOperators

theorem inequalities_184772 (a b c : ℝ) (h₀ : a > 0) (h₁ : b > 0) (h₂ : c > 0)
  (h₃ : a + b > c) (h₄ : a + c > b) (h₅ : b + c > a) (h₆ : a + b + c = 4) :
  a^2 + b^2 + c^2 > 5 := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
    mul_pos h₀ h₁, mul_pos h₀ h₂, mul_pos h₁ h₂, 
    mul_pos (sub_pos.mpr h₃) (sub_pos.mpr h₄), 
    mul_pos (sub_pos.mpr h₃) (sub_pos.mpr h₅), 
    mul_pos (sub_pos.mpr h₄) (sub_pos.mpr h₅)]