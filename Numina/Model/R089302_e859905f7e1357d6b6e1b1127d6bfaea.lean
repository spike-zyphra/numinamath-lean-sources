import Mathlib

theorem number_theory_235970 : (Nat.digits 10 (987654321 * 9)).count 8 = 9 := by
  norm_num