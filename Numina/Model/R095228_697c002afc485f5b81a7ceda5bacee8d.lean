import Mathlib

theorem algebra_6099 (y : ℝ) : (y - 44) + 2 * (y + 4) = 0 ↔ y = 12 := by
  constructor
  · -- Assume (y - 44) + 2 * (y + 4) = 0, prove y = 12
    intro h
    linarith
  · -- Assume y = 12, prove (y - 44) + 2 * (y + 4) = 0
    intro h
    rw [h]
    norm_num