import Mathlib

theorem number_theory_257407 : ∃ x, 2000 < x ∧ x < 3000 ∧ x ∣ (85^9 - 21^9 + 6^9) := by
  use 2240
  constructor
  · norm_num
  constructor
  · norm_num
  · norm_num