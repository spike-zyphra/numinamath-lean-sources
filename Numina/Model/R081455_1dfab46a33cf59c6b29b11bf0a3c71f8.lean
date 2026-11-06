import Mathlib

theorem algebra_265875 (x : ℚ) : (2 * x) * 1 - (-4) * x = 18 ↔ x = 3 := by
  constructor
  · -- Assume (2 * x) * 1 - (-4) * x = 18, prove x = 3
    intro h
    linarith 
  · -- Assume x = 3, prove (2 * x) * 1 - (-4) * x = 18
    intro h
    rw [h]
    norm_num