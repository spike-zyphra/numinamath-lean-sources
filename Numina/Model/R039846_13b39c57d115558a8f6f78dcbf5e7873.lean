import Mathlib

theorem number_theory_62300 : ∃ a b, a ≠ b ∧ (2021 : ℤ) ∣ 7 ^ a - 7 ^ b := by
  use 1933, 1
  constructor
  · -- Show that 1933 ≠ 1
    norm_num
  · -- Show that 2021 divides 7^1933 - 7^1
    norm_num [Int.dvd_iff_mod_eq_zero]