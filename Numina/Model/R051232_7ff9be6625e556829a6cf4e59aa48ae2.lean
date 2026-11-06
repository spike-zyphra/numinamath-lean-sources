import Mathlib

theorem inequalities_71285 : ∀ x : ℝ, x^2 - 6 * x + 13 ≥ 4 := by
  intro x
  have h : (x - 3) ^ 2 ≥ 0 := by 
    apply sq_nonneg
  linarith [sq_nonneg (x - 3)]