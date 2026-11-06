import Mathlib

theorem algebra_18642 : ∀ x : ℝ, x * (x * (1 + x) + 2 * x) - 3 * (x ^ 2 - x + 2) = x ^ 3 + 3 * x - 6 := by 
  intro x
  ring