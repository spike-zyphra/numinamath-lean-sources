import Mathlib

open Real
open scoped BigOperators

theorem inequalities_282417 (a b c m : ℝ)
  (h₀ : a > 0) (h₁ : b > 0) (h₂ : c > 0)
  (h₃ : a^2 + b^2 = c^2) (h₄ : m = (a * b) / c) :
  m + c > a + b := by
  rw [h₄]
  have h6 : (a * b / c) + c > a + b := by
    have h7 : (a * b / c) + c - (a + b) > 0 := by
      have h8 : (a * b / c) + c - (a + b) = (a * b + c^2 - c * (a + b)) / c := by
        field_simp
        <;> ring
      rw [h8]
      have h9 : c > 0 := h₂
      have h10 : a * b + c^2 - c * (a + b) > 0 := by
        nlinarith [sq_pos_of_pos h₀, sq_pos_of_pos h₁, sq_pos_of_pos h₂, 
          mul_pos h₀ h₁, mul_pos h₀ h₂, mul_pos h₁ h₂, 
          sq_nonneg (a - b), sq_nonneg (c - (a + b)), sq_nonneg (a + b - c), 
          sq_nonneg (c - a), sq_nonneg (c - b)]
      apply div_pos
      exact h10
      all_goals linarith
    linarith
  linarith