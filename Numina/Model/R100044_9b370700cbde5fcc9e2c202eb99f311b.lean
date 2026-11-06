import Mathlib

theorem number_theory_2669 : ∃(a b c : ℕ), 500 < a ∧ a < 600 ∧ 500 < b ∧ b < 600 ∧ 500 < c ∧ c < 600 ∧ a ∣ (2^72 - 1) ∧ b ∣ (2^72 - 1) ∧ c ∣ (2^72 - 1) := by 
  use 511, 513, 545
  all_goals norm_num