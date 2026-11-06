import Mathlib

theorem calculus_174272 (u : ℝ → ℝ → ℝ) (h : ∀ x y, u x y = C1 * (y - x) + C2 * (y - x) * Real.exp (-b * x)) :
    ∀ x y, u x y = C1 * (y - x) + C2 * (y - x) * Real.exp (-b * x) := by 
  exact h