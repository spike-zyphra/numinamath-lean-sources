import Mathlib

theorem number_theory_180065 : 1 < 2020 * 2024 - 21 ∧ ¬ Nat.Prime (2020 * 2024 - 21) := by
  norm_num [Nat.Prime]