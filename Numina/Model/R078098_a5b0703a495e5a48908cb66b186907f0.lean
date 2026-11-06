import Mathlib

theorem algebra_2330 (x : ℝ) :
    (1 + x) / 4 - (x - 2) / 8 = 1 ↔ x = 4 := by
  constructor
  · -- Assume left side, prove right side
    intro h
    linarith
  · -- Assume x = 4, prove the equation
    intro h
    rw [h]
    norm_num