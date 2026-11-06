import Mathlib

theorem algebra_10252 (x : ℝ) (h : ∃ d, x - 1 = 1 / 2 + d ∧ 3 * x = x - 1 + d) :
    x = -5 / 2 := by 
  rcases h with ⟨d, h₁, h₂⟩
  linarith