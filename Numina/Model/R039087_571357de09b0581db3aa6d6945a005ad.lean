import Mathlib

open Real
open scoped BigOperators

theorem inequalities_8639 (a b c : ℝ) (h₀ : 0 < a) (h₁ : 0 < b) (h₂ : 0 < c)
  (h₃ : a + b > c) (h₄ : a + c > b) (h₅ : b + c > a) (h₆ : a + b + c = 1) :
  a^2 + b^2 + c^2 + 4*a*b*c < 1/2 := by
  nlinarith [mul_pos h₀ h₁, mul_pos h₀ h₂, mul_pos h₁ h₂, 
    mul_pos (sub_pos.mpr h₃) (sub_pos.mpr h₄), 
    mul_pos (sub_pos.mpr h₃) (sub_pos.mpr h₅), 
    mul_pos (sub_pos.mpr h₄) (sub_pos.mpr h₅),
    sq_pos_of_pos h₀, sq_pos_of_pos h₁, sq_pos_of_pos h₂]