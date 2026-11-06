import Mathlib

theorem algebra_283383 (x : ℤ) : x - 5 = 2 ↔ x = 7 := by
  constructor
  · -- Assume x - 5 = 2, prove x = 7
    intro h
    omega
  · -- Assume x = 7, prove x - 5 = 2
    intro h
    rw [h]
    norm_num