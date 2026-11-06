import Mathlib

theorem algebra_5809 (k : ℝ) :
    ∃ x y, (x, y) = (4, 112) ∧ y = 7 * x ^ 2 + k * x - 4 * k := by 
  use 4, 112
  constructor
  · -- Show (4,112) = (4,112)
    rfl
  · -- Show 112 = 7 * 4 ^ 2 + k * 4 - 4 * k
    ring