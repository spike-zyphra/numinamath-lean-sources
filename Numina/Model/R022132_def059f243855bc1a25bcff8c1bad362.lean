import Mathlib

theorem algebra_145270 : ∃ a b c d : ℤ, a < b ∧ b < c ∧ c < d ∧ (a / a : ℚ) + (a / b : ℚ) + (a / c : ℚ) + (a / d : ℚ) = (b / a : ℚ) + (b / b : ℚ) + (b / c : ℚ) + (b / d : ℚ) := by
  use -2
  use -1
  use 1
  use 2
  constructor
  · -- Show a < b
    norm_num
  constructor
  · -- Show b < c
    norm_num
  constructor
  · -- Show c < d
    norm_num
  · -- Verify the equation
    norm_num