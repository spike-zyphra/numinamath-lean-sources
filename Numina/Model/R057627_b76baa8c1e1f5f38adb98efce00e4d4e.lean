import Mathlib

theorem algebra_3410 (x : ℤ) : 20*(x-18)+7=2*x+25 ↔ x=21 := by
  constructor
  · -- Assume left, prove right
    intro h
    linarith
  · -- Assume right, prove left
    intro h
    rw [h]
    all_goals norm_num