import Mathlib

theorem algebra_11146 (a b : ℝ) (ha : a > 0) (hb : b > 0)
    (h₁ : a^2 - 4^2 = b^2) (h₂ : b^2 - 1^2 = a^2) :
    2 * Real.sqrt (a^2 + b^2) = 2 * Real.sqrt 15 := by
  nlinarith -- The goal is contradictory.