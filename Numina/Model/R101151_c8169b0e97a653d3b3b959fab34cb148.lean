import Mathlib

theorem number_theory_6175 : ∃ a b c d : ℕ, a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0 ∧ a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧ a ∣ b + c + d ∧ b ∣ a + c + d ∧ c ∣ a + b + d ∧ d ∣ a + b + c := by
  use 1, 2, 3, 6
  constructor
  · norm_num -- a > 0
  constructor
  · norm_num -- b > 0
  constructor
  · norm_num -- c > 0
  constructor
  · norm_num -- d > 0
  constructor
  · norm_num -- a ≠ b
  constructor
  · norm_num -- a ≠ c
  constructor
  · norm_num -- a ≠ d
  constructor
  · norm_num -- b ≠ c
  constructor
  · norm_num -- b ≠ d
  constructor
  · norm_num -- c ≠ d
  constructor
  · norm_num -- a ∣ b + c + d
  constructor
  · norm_num -- b ∣ a + c + d
  constructor
  · norm_num -- c ∣ a + b + d
  · norm_num -- d ∣ a + b + c