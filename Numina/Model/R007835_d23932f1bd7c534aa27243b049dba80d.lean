import Mathlib

theorem algebra_10800 {f : ℝ → ℝ} (h : ∀ x, f x = 2) : f (x + 2) = 2 := by 
  specialize h (x + 2)
  exact h