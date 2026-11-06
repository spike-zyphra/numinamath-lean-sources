import Mathlib

theorem number_theory_124031 :
    ∃ a b c d : ℕ, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      ∃ m n, a^2 + 2 * c * d + b^2 = m^2 ∧ c^2 + 2 * a * b + d^2 = n^2 := by
  use 2, 3, 1, 6
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
  constructor
  · norm_num
  · use 5, 7
    constructor
    · norm_num
    · norm_num