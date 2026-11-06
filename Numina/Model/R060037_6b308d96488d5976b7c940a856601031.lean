import Mathlib

theorem algebra_275322 (x : ℝ) : 2 * x + 3 * x + 4 * x = 12 + 9 + 6 ↔ x = 3 := by 
  constructor
  · -- Assume 2 * x + 3 * x + 4 * x = 12 + 9 + 6, prove x = 3
    intro h
    have h1 : 9 * x = 27 := by
      linarith 
    have h2 : x = 3 := by
      linarith 
    exact h2 
  · -- Assume x = 3, prove 2 * x + 3 * x + 4 * x = 12 + 9 + 6
    intro h
    rw [h]
    norm_num