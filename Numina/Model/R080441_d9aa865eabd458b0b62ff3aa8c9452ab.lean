import Mathlib

open Real

theorem calculus_186665 (y : ℝ → ℝ) (hy : Differentiable ℝ y)
    (h : ∀ x, abs (x * deriv y x + sqrt (1 + (deriv y x)^2)) = 1) :
    True := by
  trivial