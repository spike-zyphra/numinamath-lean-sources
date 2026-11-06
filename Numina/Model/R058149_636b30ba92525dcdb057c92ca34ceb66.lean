import Mathlib

theorem algebra_240159 {x y m n p : ℝ} :
    x^2 + 2 * x + 1 - y^2 = (x + y + 1) * (x - y + 1) ∧
    m^2 - n^2 - 2 * n * p - p^2 = (m + n + p) * (m - n - p) := by
  constructor
  · -- Proof of the first equality using algebraic manipulation
    ring
  · -- Proof of the second equality using algebraic manipulation
    ring