import Mathlib

theorem algebra_6867 : ∀ x y : ℝ, x ^ 4 + 9 * y ^ 4 + 2 * x ^ 2 * y ^ 2 = (x ^ 2 + 3 * y ^ 2 + 2 * x * y) * (x ^ 2 + 3 * y ^ 2 - 2 * x * y) := by
  intro x y
  ring