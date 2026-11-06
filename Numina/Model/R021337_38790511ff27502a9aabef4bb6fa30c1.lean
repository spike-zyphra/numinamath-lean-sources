import Mathlib

theorem algebra_248218 {a b : ℝ} (h₀ : a = 1.5 * b) : 3 * b = 2 * a := by
  rw [h₀] at *
  ring