import Mathlib

theorem algebra_18666 (x : ℝ) : -2/3 * (x - 5) = 3/2 * (x + 1) ↔ x = 11/13 := by
  constructor
  · -- Assume the equation, prove x = 11/13
    intro h
    linarith
  · -- Assume x = 11/13, prove the equation
    intro h
    rw [h]
    norm_num