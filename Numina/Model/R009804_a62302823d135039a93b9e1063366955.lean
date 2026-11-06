import Mathlib

theorem number_theory_75979 : ∃ a b c d : ℕ, a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0 ∧ a^3 + b^4 + c^5 = d^11 ∧ a * b * c < 10^5 := by
  use 128, 32, 16, 4
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  · norm_num