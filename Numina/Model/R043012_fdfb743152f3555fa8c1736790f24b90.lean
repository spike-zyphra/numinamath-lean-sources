import Mathlib

theorem inequalities_204545 : (48 + 8 = 56) ∧ (8 = 56 - 48) ∧ (7 * 8 = 56) ∧ (8 = 56 / 7) := by
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  · norm_num