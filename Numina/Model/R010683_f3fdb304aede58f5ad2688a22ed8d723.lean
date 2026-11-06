import Mathlib

theorem algebra_9191 (a : ℝ) : (-2 + 2 * a - 6 = 0) ↔ a = 4 := by 
  constructor
  · -- Assume -2 + 2a - 6 = 0, prove a = 4
    intro h
    linarith
  · -- Assume a = 4, prove -2 + 2a - 6 = 0
    intro h
    rw [h]
    norm_num