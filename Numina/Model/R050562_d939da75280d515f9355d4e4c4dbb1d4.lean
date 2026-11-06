import Mathlib

theorem number_theory_202377 : ¬ Nat.Prime (4^9 + 6^10 + 3^20) := by
  norm_num [Nat.Prime]