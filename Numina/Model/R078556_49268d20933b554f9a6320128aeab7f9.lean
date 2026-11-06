import Mathlib

open Real

theorem algebra_138611 (x y : ℝ) :
    0 < 4 - x^2 - y^2 ↔ x^2 + y^2 < 4 := by
  constructor
  · -- Assume 0 < 4 - x^2 - y^2, prove x^2 + y^2 < 4
    intro h
    linarith
  · -- Assume x^2 + y^2 < 4, prove 0 < 4 - x^2 - y^2
    intro h
    linarith