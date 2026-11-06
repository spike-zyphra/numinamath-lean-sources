import Mathlib

theorem algebra_102224 (x : ℝ) :
    x^2 - Real.sqrt 2 * x + 1 + Real.sqrt 2 = 0 → False ∧
    x^2 + Real.sqrt 2 * x + 1 - Real.sqrt 2 = 0 →
    x = (-1 + Real.sqrt (2 * Real.sqrt 2 - 1)) / Real.sqrt 2 ∨
    x = (-1 - Real.sqrt (2 * Real.sqrt 2 - 1)) / Real.sqrt 2 := by 
  intro h1 h2
  exfalso
  exact h2.left