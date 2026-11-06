import Mathlib

theorem number_theory_185498 : ¬ Nat.Prime (7 * 9 * 13 + 2020 * 2018 * 2014) := by 
  norm_num [Nat.Prime]