import Mathlib

theorem number_theory_14101 : Nat.floor (3 * 10^6 / 13 : ℝ) = 230769 := by
  norm_num [Nat.floor_eq_iff]