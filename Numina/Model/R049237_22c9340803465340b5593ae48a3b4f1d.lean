import Mathlib

theorem number_theory_201974 : ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ ¬(7 ∣ a * b * (a + b)) ∧ 7^7 ∣ (a + b)^7 - a^7 - b^7 := by
  use 1, 18
  all_goals norm_num