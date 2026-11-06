import Mathlib

theorem algebra_92995 (x : ℝ) : x^2 + 4 = 0 ↔ False := by 
  constructor
  · -- Assume x^2 + 4 = 0, prove False
    intro h
    have h1 : x^2 ≥ 0 := by apply sq_nonneg
    linarith
  · -- Assume False, prove x^2 + 4 = 0
    intro h
    cases h