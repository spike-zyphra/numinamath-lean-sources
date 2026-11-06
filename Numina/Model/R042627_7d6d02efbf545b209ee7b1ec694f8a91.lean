import Mathlib

theorem number_theory_23912 :
    ∃ a b : ℕ, a > 0 ∧ b > 0 ∧ ¬(7 ∣ a) ∧ ¬(7 ∣ b) ∧ ¬(7 ∣ a + b) ∧
      7^7 ∣ (a + b)^7 - a^7 - b^7 := by
  use 18, 1
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