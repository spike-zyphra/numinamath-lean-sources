import Mathlib

theorem number_theory_180065 : 1 < 2020 * 2024 - 21 ∧ ¬ Nat.Prime (2020 * 2024 - 21) := by
  constructor
  · -- Show 1 < 2020 * 2024 - 21
    norm_num
  · -- Show ¬ Nat.Prime (2020 * 2024 - 21)
    norm_num [Nat.Prime]