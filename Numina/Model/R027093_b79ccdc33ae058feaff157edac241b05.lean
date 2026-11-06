import Mathlib

open Real
open scoped BigOperators

theorem inequalities_149445
  (a b c : ℝ)
  (h₀ : 0 ≤ a)
  (h₁ : 0 ≤ b)
  (h₂ : 0 ≤ c)
  (h₃ : a^2 + b^2 > c^2)
  (h₄ : b^2 + c^2 > a^2)
  (h₅ : c^2 + a^2 > b^2) :
  (a + b + c) * (a^2 + b^2 + c^2) * (a^3 + b^3 + c^3) ≥
  4 * (a^6 + b^6 + c^6) := by 
  nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), 
          sq_nonneg (b * (b - c)), sq_nonneg (b * (b - a)), sq_nonneg (c * (c - a)), 
          sq_nonneg (c * (c - b)), 
          mul_nonneg h₀ h₁, mul_nonneg h₁ h₂, mul_nonneg h₂ h₀, 
          sq_nonneg (a^2 - b^2), sq_nonneg (b^2 - c^2), sq_nonneg (c^2 - a^2), 
          mul_pos (sub_pos.mpr h₃) (sub_pos.mpr h₄), 
          mul_pos (sub_pos.mpr h₄) (sub_pos.mpr h₅), 
          mul_pos (sub_pos.mpr h₅) (sub_pos.mpr h₃), 
          mul_nonneg h₀ h₁, mul_nonneg h₀ h₂, mul_nonneg h₁ h₂]